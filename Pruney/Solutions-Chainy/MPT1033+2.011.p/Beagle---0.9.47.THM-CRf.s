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
% DateTime   : Thu Dec  3 10:16:52 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   99 (1863 expanded)
%              Number of leaves         :   26 ( 587 expanded)
%              Depth                    :   16
%              Number of atoms          :  164 (5079 expanded)
%              Number of equality atoms :   34 (1929 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_125,plain,(
    ! [A_31,B_32,C_33,D_34] :
      ( r2_relset_1(A_31,B_32,C_33,C_33)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_168,plain,(
    ! [C_38] :
      ( r2_relset_1('#skF_2','#skF_3',C_38,C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_34,c_125])).

tff(c_174,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_168])).

tff(c_62,plain,(
    ! [A_23] :
      ( k1_xboole_0 = A_23
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_62])).

tff(c_24,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_39,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_70,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_39])).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_30,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_138,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_partfun1(C_35,A_36)
      | ~ v1_funct_2(C_35,A_36,B_37)
      | ~ v1_funct_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | v1_xboole_0(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_141,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_138])).

tff(c_153,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_141])).

tff(c_158,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2])).

tff(c_161,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_158,c_67])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_161])).

tff(c_167,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_36,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_147,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_138])).

tff(c_157,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_147])).

tff(c_175,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_157])).

tff(c_166,plain,(
    v1_partfun1('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_26,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_176,plain,(
    ! [D_39,C_40,A_41,B_42] :
      ( D_39 = C_40
      | ~ r1_partfun1(C_40,D_39)
      | ~ v1_partfun1(D_39,A_41)
      | ~ v1_partfun1(C_40,A_41)
      | ~ m1_subset_1(D_39,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_1(D_39)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_178,plain,(
    ! [A_41,B_42] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_41)
      | ~ v1_partfun1('#skF_4',A_41)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_176])).

tff(c_181,plain,(
    ! [A_41,B_42] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_41)
      | ~ v1_partfun1('#skF_4',A_41)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_178])).

tff(c_185,plain,(
    ! [A_44,B_45] :
      ( ~ v1_partfun1('#skF_5',A_44)
      | ~ v1_partfun1('#skF_4',A_44)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_188,plain,
    ( ~ v1_partfun1('#skF_5','#skF_2')
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_28,c_185])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_175,c_166,c_188])).

tff(c_199,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_22,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_203,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_22])).

tff(c_212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_203])).

tff(c_214,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_238,plain,(
    ! [A_47] :
      ( A_47 = '#skF_3'
      | ~ v1_xboole_0(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_2])).

tff(c_242,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_238])).

tff(c_246,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_214])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_261,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_246,c_10])).

tff(c_213,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_219,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_213])).

tff(c_245,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_219])).

tff(c_292,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_245,c_242,c_34])).

tff(c_294,plain,(
    ! [B_51,A_52] :
      ( v1_xboole_0(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_300,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_292,c_294])).

tff(c_306,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_300])).

tff(c_237,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_2])).

tff(c_243,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_237])).

tff(c_314,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_306,c_243])).

tff(c_293,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_245,c_242,c_28])).

tff(c_297,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_293,c_294])).

tff(c_303,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_297])).

tff(c_310,plain,(
    '#skF_5' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_303,c_243])).

tff(c_316,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_293])).

tff(c_368,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_314,c_316])).

tff(c_331,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_4',B_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_314,c_261])).

tff(c_375,plain,(
    ! [A_56,B_57,C_58,D_59] :
      ( r2_relset_1(A_56,B_57,C_58,C_58)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_377,plain,(
    ! [B_3,C_58,D_59] :
      ( r2_relset_1('#skF_4',B_3,C_58,C_58)
      | ~ m1_subset_1(D_59,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_3))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_375])).

tff(c_378,plain,(
    ! [B_3,C_58,D_59] :
      ( r2_relset_1('#skF_4',B_3,C_58,C_58)
      | ~ m1_subset_1(D_59,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_58,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_377])).

tff(c_417,plain,(
    ! [D_59] : ~ m1_subset_1(D_59,k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_417,c_368])).

tff(c_421,plain,(
    ! [B_64,C_65] :
      ( r2_relset_1('#skF_4',B_64,C_65,C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_424,plain,(
    ! [B_64] : r2_relset_1('#skF_4',B_64,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_368,c_421])).

tff(c_285,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_242,c_22])).

tff(c_318,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_285])).

tff(c_404,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_314,c_314,c_318])).

tff(c_435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_404])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.31  
% 2.18/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.31  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.18/1.31  
% 2.18/1.31  %Foreground sorts:
% 2.18/1.31  
% 2.18/1.31  
% 2.18/1.31  %Background operators:
% 2.18/1.31  
% 2.18/1.31  
% 2.18/1.31  %Foreground operators:
% 2.18/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.31  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.18/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.18/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.18/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.31  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.18/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.18/1.31  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.18/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.31  
% 2.42/1.33  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.42/1.33  tff(f_104, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_2)).
% 2.42/1.33  tff(f_50, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.42/1.33  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.42/1.33  tff(f_64, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.42/1.33  tff(f_81, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 2.42/1.33  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.42/1.33  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.42/1.33  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.33  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.42/1.33  tff(c_125, plain, (![A_31, B_32, C_33, D_34]: (r2_relset_1(A_31, B_32, C_33, C_33) | ~m1_subset_1(D_34, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.42/1.33  tff(c_168, plain, (![C_38]: (r2_relset_1('#skF_2', '#skF_3', C_38, C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_34, c_125])).
% 2.42/1.33  tff(c_174, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_168])).
% 2.42/1.33  tff(c_62, plain, (![A_23]: (k1_xboole_0=A_23 | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.42/1.33  tff(c_66, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_62])).
% 2.42/1.33  tff(c_24, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.42/1.33  tff(c_39, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_24])).
% 2.42/1.33  tff(c_70, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_39])).
% 2.42/1.33  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.42/1.33  tff(c_30, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.42/1.33  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.42/1.33  tff(c_138, plain, (![C_35, A_36, B_37]: (v1_partfun1(C_35, A_36) | ~v1_funct_2(C_35, A_36, B_37) | ~v1_funct_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | v1_xboole_0(B_37))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.42/1.33  tff(c_141, plain, (v1_partfun1('#skF_5', '#skF_2') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_138])).
% 2.42/1.33  tff(c_153, plain, (v1_partfun1('#skF_5', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_141])).
% 2.42/1.33  tff(c_158, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_153])).
% 2.42/1.33  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.42/1.33  tff(c_67, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2])).
% 2.42/1.33  tff(c_161, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_158, c_67])).
% 2.42/1.33  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_161])).
% 2.42/1.33  tff(c_167, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_153])).
% 2.42/1.33  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.42/1.33  tff(c_36, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.42/1.33  tff(c_147, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_138])).
% 2.42/1.33  tff(c_157, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_147])).
% 2.42/1.33  tff(c_175, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_167, c_157])).
% 2.42/1.33  tff(c_166, plain, (v1_partfun1('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_153])).
% 2.42/1.33  tff(c_26, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.42/1.33  tff(c_176, plain, (![D_39, C_40, A_41, B_42]: (D_39=C_40 | ~r1_partfun1(C_40, D_39) | ~v1_partfun1(D_39, A_41) | ~v1_partfun1(C_40, A_41) | ~m1_subset_1(D_39, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_1(D_39) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_1(C_40))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.42/1.33  tff(c_178, plain, (![A_41, B_42]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_41) | ~v1_partfun1('#skF_4', A_41) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_176])).
% 2.42/1.33  tff(c_181, plain, (![A_41, B_42]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_41) | ~v1_partfun1('#skF_4', A_41) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_178])).
% 2.42/1.33  tff(c_185, plain, (![A_44, B_45]: (~v1_partfun1('#skF_5', A_44) | ~v1_partfun1('#skF_4', A_44) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(splitLeft, [status(thm)], [c_181])).
% 2.42/1.33  tff(c_188, plain, (~v1_partfun1('#skF_5', '#skF_2') | ~v1_partfun1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_28, c_185])).
% 2.42/1.33  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_175, c_166, c_188])).
% 2.42/1.33  tff(c_199, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_181])).
% 2.42/1.33  tff(c_22, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.42/1.33  tff(c_203, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_22])).
% 2.42/1.33  tff(c_212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_174, c_203])).
% 2.42/1.33  tff(c_214, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 2.42/1.33  tff(c_238, plain, (![A_47]: (A_47='#skF_3' | ~v1_xboole_0(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_2])).
% 2.42/1.33  tff(c_242, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_4, c_238])).
% 2.42/1.33  tff(c_246, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_242, c_214])).
% 2.42/1.33  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.42/1.33  tff(c_261, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_246, c_246, c_10])).
% 2.42/1.33  tff(c_213, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.42/1.33  tff(c_219, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_214, c_213])).
% 2.42/1.33  tff(c_245, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_242, c_219])).
% 2.42/1.33  tff(c_292, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_261, c_245, c_242, c_34])).
% 2.42/1.33  tff(c_294, plain, (![B_51, A_52]: (v1_xboole_0(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.42/1.33  tff(c_300, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_292, c_294])).
% 2.42/1.33  tff(c_306, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_300])).
% 2.42/1.33  tff(c_237, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_2])).
% 2.42/1.33  tff(c_243, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_237])).
% 2.42/1.33  tff(c_314, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_306, c_243])).
% 2.42/1.33  tff(c_293, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_261, c_245, c_242, c_28])).
% 2.42/1.33  tff(c_297, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_293, c_294])).
% 2.42/1.33  tff(c_303, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_297])).
% 2.42/1.33  tff(c_310, plain, ('#skF_5'='#skF_1'), inference(resolution, [status(thm)], [c_303, c_243])).
% 2.42/1.33  tff(c_316, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_293])).
% 2.42/1.33  tff(c_368, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_314, c_316])).
% 2.42/1.33  tff(c_331, plain, (![B_3]: (k2_zfmisc_1('#skF_4', B_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_314, c_314, c_261])).
% 2.42/1.33  tff(c_375, plain, (![A_56, B_57, C_58, D_59]: (r2_relset_1(A_56, B_57, C_58, C_58) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.42/1.33  tff(c_377, plain, (![B_3, C_58, D_59]: (r2_relset_1('#skF_4', B_3, C_58, C_58) | ~m1_subset_1(D_59, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_3))))), inference(superposition, [status(thm), theory('equality')], [c_331, c_375])).
% 2.42/1.33  tff(c_378, plain, (![B_3, C_58, D_59]: (r2_relset_1('#skF_4', B_3, C_58, C_58) | ~m1_subset_1(D_59, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_58, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_331, c_377])).
% 2.42/1.33  tff(c_417, plain, (![D_59]: (~m1_subset_1(D_59, k1_zfmisc_1('#skF_4')))), inference(splitLeft, [status(thm)], [c_378])).
% 2.42/1.33  tff(c_419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_417, c_368])).
% 2.42/1.33  tff(c_421, plain, (![B_64, C_65]: (r2_relset_1('#skF_4', B_64, C_65, C_65) | ~m1_subset_1(C_65, k1_zfmisc_1('#skF_4')))), inference(splitRight, [status(thm)], [c_378])).
% 2.42/1.33  tff(c_424, plain, (![B_64]: (r2_relset_1('#skF_4', B_64, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_368, c_421])).
% 2.42/1.33  tff(c_285, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_245, c_242, c_22])).
% 2.42/1.33  tff(c_318, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_310, c_285])).
% 2.42/1.33  tff(c_404, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_314, c_314, c_314, c_318])).
% 2.42/1.33  tff(c_435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_424, c_404])).
% 2.42/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.33  
% 2.42/1.33  Inference rules
% 2.42/1.33  ----------------------
% 2.42/1.33  #Ref     : 0
% 2.42/1.33  #Sup     : 88
% 2.42/1.33  #Fact    : 0
% 2.42/1.33  #Define  : 0
% 2.42/1.33  #Split   : 6
% 2.42/1.33  #Chain   : 0
% 2.42/1.33  #Close   : 0
% 2.42/1.33  
% 2.42/1.33  Ordering : KBO
% 2.42/1.33  
% 2.42/1.33  Simplification rules
% 2.42/1.33  ----------------------
% 2.42/1.33  #Subsume      : 4
% 2.42/1.33  #Demod        : 102
% 2.42/1.33  #Tautology    : 71
% 2.42/1.33  #SimpNegUnit  : 3
% 2.42/1.33  #BackRed      : 37
% 2.42/1.33  
% 2.42/1.33  #Partial instantiations: 0
% 2.42/1.33  #Strategies tried      : 1
% 2.42/1.33  
% 2.42/1.33  Timing (in seconds)
% 2.42/1.33  ----------------------
% 2.42/1.34  Preprocessing        : 0.31
% 2.42/1.34  Parsing              : 0.17
% 2.42/1.34  CNF conversion       : 0.02
% 2.42/1.34  Main loop            : 0.25
% 2.42/1.34  Inferencing          : 0.09
% 2.42/1.34  Reduction            : 0.09
% 2.42/1.34  Demodulation         : 0.06
% 2.42/1.34  BG Simplification    : 0.01
% 2.42/1.34  Subsumption          : 0.03
% 2.42/1.34  Abstraction          : 0.01
% 2.42/1.34  MUC search           : 0.00
% 2.42/1.34  Cooper               : 0.00
% 2.42/1.34  Total                : 0.60
% 2.42/1.34  Index Insertion      : 0.00
% 2.42/1.34  Index Deletion       : 0.00
% 2.42/1.34  Index Matching       : 0.00
% 2.42/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
