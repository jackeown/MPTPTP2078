%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:01 EST 2020

% Result     : Theorem 13.73s
% Output     : CNFRefutation 13.82s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 484 expanded)
%              Number of leaves         :   46 ( 195 expanded)
%              Depth                    :   21
%              Number of atoms          :  305 (2001 expanded)
%              Number of equality atoms :  118 ( 707 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_199,negated_conjecture,(
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

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_130,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_114,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_118,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_173,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_128,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_102,axiom,(
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

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_147,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_60,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_112,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_125,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_112])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_48,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_6,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_84,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6])).

tff(c_70,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_529,plain,(
    ! [F_134,A_139,E_137,D_136,B_138,C_135] :
      ( m1_subset_1(k1_partfun1(A_139,B_138,C_135,D_136,E_137,F_134),k1_zfmisc_1(k2_zfmisc_1(A_139,D_136)))
      | ~ m1_subset_1(F_134,k1_zfmisc_1(k2_zfmisc_1(C_135,D_136)))
      | ~ v1_funct_1(F_134)
      | ~ m1_subset_1(E_137,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138)))
      | ~ v1_funct_1(E_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_44,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_68,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_369,plain,(
    ! [D_101,C_102,A_103,B_104] :
      ( D_101 = C_102
      | ~ r2_relset_1(A_103,B_104,C_102,D_101)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_377,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_369])).

tff(c_392,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_377])).

tff(c_405,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_392])).

tff(c_545,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_529,c_405])).

tff(c_592,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_545])).

tff(c_593,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_392])).

tff(c_1661,plain,(
    ! [D_227,B_226,A_229,C_228,E_225] :
      ( k1_xboole_0 = C_228
      | v2_funct_1(E_225)
      | k2_relset_1(A_229,B_226,D_227) != B_226
      | ~ v2_funct_1(k1_partfun1(A_229,B_226,B_226,C_228,D_227,E_225))
      | ~ m1_subset_1(E_225,k1_zfmisc_1(k2_zfmisc_1(B_226,C_228)))
      | ~ v1_funct_2(E_225,B_226,C_228)
      | ~ v1_funct_1(E_225)
      | ~ m1_subset_1(D_227,k1_zfmisc_1(k2_zfmisc_1(A_229,B_226)))
      | ~ v1_funct_2(D_227,A_229,B_226)
      | ~ v1_funct_1(D_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1667,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_593,c_1661])).

tff(c_1675,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_72,c_84,c_70,c_1667])).

tff(c_1676,plain,(
    v2_funct_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1675])).

tff(c_153,plain,(
    ! [A_66,B_67,C_68] :
      ( k2_relset_1(A_66,B_67,C_68) = k2_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_159,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_153])).

tff(c_165,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_159])).

tff(c_1129,plain,(
    ! [B_194,F_192,A_190,C_195,E_193,D_191] :
      ( k1_partfun1(A_190,B_194,C_195,D_191,E_193,F_192) = k5_relat_1(E_193,F_192)
      | ~ m1_subset_1(F_192,k1_zfmisc_1(k2_zfmisc_1(C_195,D_191)))
      | ~ v1_funct_1(F_192)
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(A_190,B_194)))
      | ~ v1_funct_1(E_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1135,plain,(
    ! [A_190,B_194,E_193] :
      ( k1_partfun1(A_190,B_194,'#skF_2','#skF_1',E_193,'#skF_4') = k5_relat_1(E_193,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(A_190,B_194)))
      | ~ v1_funct_1(E_193) ) ),
    inference(resolution,[status(thm)],[c_72,c_1129])).

tff(c_1759,plain,(
    ! [A_231,B_232,E_233] :
      ( k1_partfun1(A_231,B_232,'#skF_2','#skF_1',E_233,'#skF_4') = k5_relat_1(E_233,'#skF_4')
      | ~ m1_subset_1(E_233,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232)))
      | ~ v1_funct_1(E_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1135])).

tff(c_1783,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1759])).

tff(c_1806,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_593,c_1783])).

tff(c_124,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_112])).

tff(c_195,plain,(
    ! [A_72,B_73,C_74,D_75] :
      ( k8_relset_1(A_72,B_73,C_74,D_75) = k10_relat_1(C_74,D_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_204,plain,(
    ! [D_75] : k8_relset_1('#skF_2','#skF_1','#skF_4',D_75) = k10_relat_1('#skF_4',D_75) ),
    inference(resolution,[status(thm)],[c_72,c_195])).

tff(c_269,plain,(
    ! [A_86,B_87,C_88] :
      ( k8_relset_1(A_86,B_87,C_88,B_87) = k1_relset_1(A_86,B_87,C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_275,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_4','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_269])).

tff(c_281,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k10_relat_1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_275])).

tff(c_338,plain,(
    ! [B_98,A_99,C_100] :
      ( k1_xboole_0 = B_98
      | k1_relset_1(A_99,B_98,C_100) = A_99
      | ~ v1_funct_2(C_100,A_99,B_98)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_99,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_347,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_338])).

tff(c_356,plain,
    ( k1_xboole_0 = '#skF_1'
    | k10_relat_1('#skF_4','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_281,c_347])).

tff(c_357,plain,(
    k10_relat_1('#skF_4','#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_356])).

tff(c_66,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_2,plain,(
    ! [A_1] :
      ( k10_relat_1(A_1,k2_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_170,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_2])).

tff(c_174,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_170])).

tff(c_203,plain,(
    ! [D_75] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_75) = k10_relat_1('#skF_3',D_75) ),
    inference(resolution,[status(thm)],[c_78,c_195])).

tff(c_273,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') = k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_269])).

tff(c_279,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_203,c_273])).

tff(c_344,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_338])).

tff(c_352,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_279,c_344])).

tff(c_353,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_352])).

tff(c_8,plain,(
    ! [A_3,B_5] :
      ( k2_funct_1(A_3) = B_5
      | k6_relat_1(k2_relat_1(A_3)) != k5_relat_1(B_5,A_3)
      | k2_relat_1(B_5) != k1_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_656,plain,(
    ! [A_154,B_155] :
      ( k2_funct_1(A_154) = B_155
      | k6_partfun1(k2_relat_1(A_154)) != k5_relat_1(B_155,A_154)
      | k2_relat_1(B_155) != k1_relat_1(A_154)
      | ~ v2_funct_1(A_154)
      | ~ v1_funct_1(B_155)
      | ~ v1_relat_1(B_155)
      | ~ v1_funct_1(A_154)
      | ~ v1_relat_1(A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_8])).

tff(c_658,plain,(
    ! [B_155] :
      ( k2_funct_1('#skF_3') = B_155
      | k5_relat_1(B_155,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_155) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_155)
      | ~ v1_relat_1(B_155)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_656])).

tff(c_662,plain,(
    ! [B_157] :
      ( k2_funct_1('#skF_3') = B_157
      | k5_relat_1(B_157,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_157) != '#skF_1'
      | ~ v1_funct_1(B_157)
      | ~ v1_relat_1(B_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_82,c_66,c_353,c_658])).

tff(c_665,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_125,c_662])).

tff(c_674,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_665])).

tff(c_675,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_674])).

tff(c_680,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_675])).

tff(c_143,plain,(
    ! [A_63,B_64,D_65] :
      ( r2_relset_1(A_63,B_64,D_65,D_65)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_150,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_44,c_143])).

tff(c_166,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_153])).

tff(c_1080,plain,(
    ! [A_185,B_186,C_187,D_188] :
      ( k2_relset_1(A_185,B_186,C_187) = B_186
      | ~ r2_relset_1(B_186,B_186,k1_partfun1(B_186,A_185,A_185,B_186,D_188,C_187),k6_partfun1(B_186))
      | ~ m1_subset_1(D_188,k1_zfmisc_1(k2_zfmisc_1(B_186,A_185)))
      | ~ v1_funct_2(D_188,B_186,A_185)
      | ~ v1_funct_1(D_188)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186)))
      | ~ v1_funct_2(C_187,A_185,B_186)
      | ~ v1_funct_1(C_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1086,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_1080])).

tff(c_1090,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_82,c_80,c_78,c_150,c_166,c_1086])).

tff(c_1092,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_680,c_1090])).

tff(c_1094,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_675])).

tff(c_1102,plain,
    ( k10_relat_1('#skF_4','#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1094,c_2])).

tff(c_1108,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_357,c_1102])).

tff(c_83,plain,(
    ! [A_3,B_5] :
      ( k2_funct_1(A_3) = B_5
      | k6_partfun1(k2_relat_1(A_3)) != k5_relat_1(B_5,A_3)
      | k2_relat_1(B_5) != k1_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_8])).

tff(c_1099,plain,(
    ! [B_5] :
      ( k2_funct_1('#skF_4') = B_5
      | k5_relat_1(B_5,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_5) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1094,c_83])).

tff(c_1106,plain,(
    ! [B_5] :
      ( k2_funct_1('#skF_4') = B_5
      | k5_relat_1(B_5,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_5) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_76,c_1099])).

tff(c_15353,plain,(
    ! [B_664] :
      ( k2_funct_1('#skF_4') = B_664
      | k5_relat_1(B_664,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_664) != '#skF_2'
      | ~ v1_funct_1(B_664)
      | ~ v1_relat_1(B_664) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1676,c_1108,c_1106])).

tff(c_15641,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_124,c_15353])).

tff(c_15860,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_165,c_1806,c_15641])).

tff(c_10,plain,(
    ! [A_6] :
      ( k2_funct_1(k2_funct_1(A_6)) = A_6
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_15866,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_15860,c_10])).

tff(c_15870,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_76,c_1676,c_15866])).

tff(c_15872,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_15870])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:38:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.73/6.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.82/6.63  
% 13.82/6.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.82/6.63  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.82/6.63  
% 13.82/6.63  %Foreground sorts:
% 13.82/6.63  
% 13.82/6.63  
% 13.82/6.63  %Background operators:
% 13.82/6.63  
% 13.82/6.63  
% 13.82/6.63  %Foreground operators:
% 13.82/6.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.82/6.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.82/6.63  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 13.82/6.63  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.82/6.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.82/6.63  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 13.82/6.63  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 13.82/6.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.82/6.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.82/6.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.82/6.63  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 13.82/6.63  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.82/6.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.82/6.63  tff('#skF_2', type, '#skF_2': $i).
% 13.82/6.63  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 13.82/6.63  tff('#skF_3', type, '#skF_3': $i).
% 13.82/6.63  tff('#skF_1', type, '#skF_1': $i).
% 13.82/6.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.82/6.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.82/6.63  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 13.82/6.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.82/6.63  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 13.82/6.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.82/6.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.82/6.63  tff('#skF_4', type, '#skF_4': $i).
% 13.82/6.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.82/6.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.82/6.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.82/6.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.82/6.63  
% 13.82/6.65  tff(f_199, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 13.82/6.65  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.82/6.65  tff(f_130, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 13.82/6.65  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 13.82/6.65  tff(f_114, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 13.82/6.65  tff(f_118, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 13.82/6.65  tff(f_78, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 13.82/6.65  tff(f_173, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 13.82/6.65  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.82/6.65  tff(f_128, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 13.82/6.65  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 13.82/6.65  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 13.82/6.65  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 13.82/6.65  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 13.82/6.65  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 13.82/6.65  tff(f_147, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 13.82/6.65  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 13.82/6.65  tff(c_60, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_199])).
% 13.82/6.65  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 13.82/6.65  tff(c_112, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.82/6.65  tff(c_125, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_112])).
% 13.82/6.65  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_199])).
% 13.82/6.65  tff(c_64, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_199])).
% 13.82/6.65  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 13.82/6.65  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 13.82/6.65  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 13.82/6.65  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_199])).
% 13.82/6.65  tff(c_48, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_130])).
% 13.82/6.65  tff(c_6, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.82/6.65  tff(c_84, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6])).
% 13.82/6.65  tff(c_70, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_199])).
% 13.82/6.65  tff(c_529, plain, (![F_134, A_139, E_137, D_136, B_138, C_135]: (m1_subset_1(k1_partfun1(A_139, B_138, C_135, D_136, E_137, F_134), k1_zfmisc_1(k2_zfmisc_1(A_139, D_136))) | ~m1_subset_1(F_134, k1_zfmisc_1(k2_zfmisc_1(C_135, D_136))) | ~v1_funct_1(F_134) | ~m1_subset_1(E_137, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))) | ~v1_funct_1(E_137))), inference(cnfTransformation, [status(thm)], [f_114])).
% 13.82/6.65  tff(c_44, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 13.82/6.65  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_199])).
% 13.82/6.65  tff(c_369, plain, (![D_101, C_102, A_103, B_104]: (D_101=C_102 | ~r2_relset_1(A_103, B_104, C_102, D_101) | ~m1_subset_1(D_101, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 13.82/6.65  tff(c_377, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_369])).
% 13.82/6.65  tff(c_392, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_377])).
% 13.82/6.65  tff(c_405, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_392])).
% 13.82/6.65  tff(c_545, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_529, c_405])).
% 13.82/6.65  tff(c_592, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_545])).
% 13.82/6.65  tff(c_593, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_392])).
% 13.82/6.65  tff(c_1661, plain, (![D_227, B_226, A_229, C_228, E_225]: (k1_xboole_0=C_228 | v2_funct_1(E_225) | k2_relset_1(A_229, B_226, D_227)!=B_226 | ~v2_funct_1(k1_partfun1(A_229, B_226, B_226, C_228, D_227, E_225)) | ~m1_subset_1(E_225, k1_zfmisc_1(k2_zfmisc_1(B_226, C_228))) | ~v1_funct_2(E_225, B_226, C_228) | ~v1_funct_1(E_225) | ~m1_subset_1(D_227, k1_zfmisc_1(k2_zfmisc_1(A_229, B_226))) | ~v1_funct_2(D_227, A_229, B_226) | ~v1_funct_1(D_227))), inference(cnfTransformation, [status(thm)], [f_173])).
% 13.82/6.65  tff(c_1667, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_593, c_1661])).
% 13.82/6.65  tff(c_1675, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_72, c_84, c_70, c_1667])).
% 13.82/6.65  tff(c_1676, plain, (v2_funct_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_1675])).
% 13.82/6.65  tff(c_153, plain, (![A_66, B_67, C_68]: (k2_relset_1(A_66, B_67, C_68)=k2_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.82/6.65  tff(c_159, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_153])).
% 13.82/6.65  tff(c_165, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_159])).
% 13.82/6.65  tff(c_1129, plain, (![B_194, F_192, A_190, C_195, E_193, D_191]: (k1_partfun1(A_190, B_194, C_195, D_191, E_193, F_192)=k5_relat_1(E_193, F_192) | ~m1_subset_1(F_192, k1_zfmisc_1(k2_zfmisc_1(C_195, D_191))) | ~v1_funct_1(F_192) | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(A_190, B_194))) | ~v1_funct_1(E_193))), inference(cnfTransformation, [status(thm)], [f_128])).
% 13.82/6.65  tff(c_1135, plain, (![A_190, B_194, E_193]: (k1_partfun1(A_190, B_194, '#skF_2', '#skF_1', E_193, '#skF_4')=k5_relat_1(E_193, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(A_190, B_194))) | ~v1_funct_1(E_193))), inference(resolution, [status(thm)], [c_72, c_1129])).
% 13.82/6.65  tff(c_1759, plain, (![A_231, B_232, E_233]: (k1_partfun1(A_231, B_232, '#skF_2', '#skF_1', E_233, '#skF_4')=k5_relat_1(E_233, '#skF_4') | ~m1_subset_1(E_233, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))) | ~v1_funct_1(E_233))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1135])).
% 13.82/6.65  tff(c_1783, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1759])).
% 13.82/6.65  tff(c_1806, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_593, c_1783])).
% 13.82/6.65  tff(c_124, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_112])).
% 13.82/6.65  tff(c_195, plain, (![A_72, B_73, C_74, D_75]: (k8_relset_1(A_72, B_73, C_74, D_75)=k10_relat_1(C_74, D_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.82/6.65  tff(c_204, plain, (![D_75]: (k8_relset_1('#skF_2', '#skF_1', '#skF_4', D_75)=k10_relat_1('#skF_4', D_75))), inference(resolution, [status(thm)], [c_72, c_195])).
% 13.82/6.65  tff(c_269, plain, (![A_86, B_87, C_88]: (k8_relset_1(A_86, B_87, C_88, B_87)=k1_relset_1(A_86, B_87, C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.82/6.65  tff(c_275, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_269])).
% 13.82/6.65  tff(c_281, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k10_relat_1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_275])).
% 13.82/6.65  tff(c_338, plain, (![B_98, A_99, C_100]: (k1_xboole_0=B_98 | k1_relset_1(A_99, B_98, C_100)=A_99 | ~v1_funct_2(C_100, A_99, B_98) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.82/6.65  tff(c_347, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_338])).
% 13.82/6.65  tff(c_356, plain, (k1_xboole_0='#skF_1' | k10_relat_1('#skF_4', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_281, c_347])).
% 13.82/6.65  tff(c_357, plain, (k10_relat_1('#skF_4', '#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_64, c_356])).
% 13.82/6.65  tff(c_66, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 13.82/6.65  tff(c_62, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_199])).
% 13.82/6.65  tff(c_2, plain, (![A_1]: (k10_relat_1(A_1, k2_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.82/6.65  tff(c_170, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_165, c_2])).
% 13.82/6.65  tff(c_174, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_170])).
% 13.82/6.65  tff(c_203, plain, (![D_75]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_75)=k10_relat_1('#skF_3', D_75))), inference(resolution, [status(thm)], [c_78, c_195])).
% 13.82/6.65  tff(c_273, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_78, c_269])).
% 13.82/6.65  tff(c_279, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_203, c_273])).
% 13.82/6.65  tff(c_344, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_338])).
% 13.82/6.65  tff(c_352, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_279, c_344])).
% 13.82/6.65  tff(c_353, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_62, c_352])).
% 13.82/6.65  tff(c_8, plain, (![A_3, B_5]: (k2_funct_1(A_3)=B_5 | k6_relat_1(k2_relat_1(A_3))!=k5_relat_1(B_5, A_3) | k2_relat_1(B_5)!=k1_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.82/6.65  tff(c_656, plain, (![A_154, B_155]: (k2_funct_1(A_154)=B_155 | k6_partfun1(k2_relat_1(A_154))!=k5_relat_1(B_155, A_154) | k2_relat_1(B_155)!=k1_relat_1(A_154) | ~v2_funct_1(A_154) | ~v1_funct_1(B_155) | ~v1_relat_1(B_155) | ~v1_funct_1(A_154) | ~v1_relat_1(A_154))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_8])).
% 13.82/6.65  tff(c_658, plain, (![B_155]: (k2_funct_1('#skF_3')=B_155 | k5_relat_1(B_155, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_155)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_155) | ~v1_relat_1(B_155) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_656])).
% 13.82/6.65  tff(c_662, plain, (![B_157]: (k2_funct_1('#skF_3')=B_157 | k5_relat_1(B_157, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_157)!='#skF_1' | ~v1_funct_1(B_157) | ~v1_relat_1(B_157))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_82, c_66, c_353, c_658])).
% 13.82/6.65  tff(c_665, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_125, c_662])).
% 13.82/6.65  tff(c_674, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_665])).
% 13.82/6.65  tff(c_675, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_60, c_674])).
% 13.82/6.65  tff(c_680, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_675])).
% 13.82/6.65  tff(c_143, plain, (![A_63, B_64, D_65]: (r2_relset_1(A_63, B_64, D_65, D_65) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 13.82/6.65  tff(c_150, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_44, c_143])).
% 13.82/6.65  tff(c_166, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_153])).
% 13.82/6.65  tff(c_1080, plain, (![A_185, B_186, C_187, D_188]: (k2_relset_1(A_185, B_186, C_187)=B_186 | ~r2_relset_1(B_186, B_186, k1_partfun1(B_186, A_185, A_185, B_186, D_188, C_187), k6_partfun1(B_186)) | ~m1_subset_1(D_188, k1_zfmisc_1(k2_zfmisc_1(B_186, A_185))) | ~v1_funct_2(D_188, B_186, A_185) | ~v1_funct_1(D_188) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))) | ~v1_funct_2(C_187, A_185, B_186) | ~v1_funct_1(C_187))), inference(cnfTransformation, [status(thm)], [f_147])).
% 13.82/6.65  tff(c_1086, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_593, c_1080])).
% 13.82/6.65  tff(c_1090, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_82, c_80, c_78, c_150, c_166, c_1086])).
% 13.82/6.65  tff(c_1092, plain, $false, inference(negUnitSimplification, [status(thm)], [c_680, c_1090])).
% 13.82/6.65  tff(c_1094, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_675])).
% 13.82/6.65  tff(c_1102, plain, (k10_relat_1('#skF_4', '#skF_1')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1094, c_2])).
% 13.82/6.65  tff(c_1108, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_357, c_1102])).
% 13.82/6.65  tff(c_83, plain, (![A_3, B_5]: (k2_funct_1(A_3)=B_5 | k6_partfun1(k2_relat_1(A_3))!=k5_relat_1(B_5, A_3) | k2_relat_1(B_5)!=k1_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_8])).
% 13.82/6.65  tff(c_1099, plain, (![B_5]: (k2_funct_1('#skF_4')=B_5 | k5_relat_1(B_5, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_5)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_5) | ~v1_relat_1(B_5) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1094, c_83])).
% 13.82/6.65  tff(c_1106, plain, (![B_5]: (k2_funct_1('#skF_4')=B_5 | k5_relat_1(B_5, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_5)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_5) | ~v1_relat_1(B_5))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_76, c_1099])).
% 13.82/6.65  tff(c_15353, plain, (![B_664]: (k2_funct_1('#skF_4')=B_664 | k5_relat_1(B_664, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_664)!='#skF_2' | ~v1_funct_1(B_664) | ~v1_relat_1(B_664))), inference(demodulation, [status(thm), theory('equality')], [c_1676, c_1108, c_1106])).
% 13.82/6.65  tff(c_15641, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_124, c_15353])).
% 13.82/6.65  tff(c_15860, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_165, c_1806, c_15641])).
% 13.82/6.65  tff(c_10, plain, (![A_6]: (k2_funct_1(k2_funct_1(A_6))=A_6 | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.82/6.65  tff(c_15866, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_15860, c_10])).
% 13.82/6.65  tff(c_15870, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_76, c_1676, c_15866])).
% 13.82/6.65  tff(c_15872, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_15870])).
% 13.82/6.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.82/6.65  
% 13.82/6.65  Inference rules
% 13.82/6.65  ----------------------
% 13.82/6.65  #Ref     : 0
% 13.82/6.65  #Sup     : 3381
% 13.82/6.65  #Fact    : 0
% 13.82/6.65  #Define  : 0
% 13.82/6.65  #Split   : 46
% 13.82/6.65  #Chain   : 0
% 13.82/6.65  #Close   : 0
% 13.82/6.65  
% 13.82/6.65  Ordering : KBO
% 13.82/6.65  
% 13.82/6.65  Simplification rules
% 13.82/6.65  ----------------------
% 13.82/6.65  #Subsume      : 129
% 13.82/6.65  #Demod        : 5571
% 13.82/6.65  #Tautology    : 566
% 13.82/6.65  #SimpNegUnit  : 281
% 13.82/6.65  #BackRed      : 52
% 13.82/6.65  
% 13.82/6.65  #Partial instantiations: 0
% 13.82/6.65  #Strategies tried      : 1
% 13.82/6.65  
% 13.82/6.65  Timing (in seconds)
% 13.82/6.65  ----------------------
% 13.82/6.66  Preprocessing        : 0.38
% 13.82/6.66  Parsing              : 0.20
% 13.82/6.66  CNF conversion       : 0.03
% 13.82/6.66  Main loop            : 5.49
% 13.82/6.66  Inferencing          : 1.14
% 13.82/6.66  Reduction            : 2.83
% 13.82/6.66  Demodulation         : 2.34
% 13.82/6.66  BG Simplification    : 0.11
% 13.82/6.66  Subsumption          : 1.15
% 13.82/6.66  Abstraction          : 0.19
% 13.82/6.66  MUC search           : 0.00
% 13.82/6.66  Cooper               : 0.00
% 13.82/6.66  Total                : 5.92
% 13.82/6.66  Index Insertion      : 0.00
% 13.82/6.66  Index Deletion       : 0.00
% 13.82/6.66  Index Matching       : 0.00
% 13.82/6.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
