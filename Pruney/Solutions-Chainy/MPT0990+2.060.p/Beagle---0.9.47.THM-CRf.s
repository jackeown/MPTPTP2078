%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:04 EST 2020

% Result     : Theorem 6.58s
% Output     : CNFRefutation 6.92s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 672 expanded)
%              Number of leaves         :   45 ( 260 expanded)
%              Depth                    :   15
%              Number of atoms          :  381 (2738 expanded)
%              Number of equality atoms :  130 ( 950 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(f_209,negated_conjecture,(
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

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_124,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_40,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_183,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_112,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_122,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_108,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_141,axiom,(
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

tff(f_167,axiom,(
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

tff(c_64,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_134,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_146,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_134])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_147,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_134])).

tff(c_86,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_70,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_48,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_6,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_92,plain,(
    ! [A_8] : k1_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_84,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_74,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_4126,plain,(
    ! [A_253,C_254,B_255] :
      ( k6_partfun1(A_253) = k5_relat_1(C_254,k2_funct_1(C_254))
      | k1_xboole_0 = B_255
      | ~ v2_funct_1(C_254)
      | k2_relset_1(A_253,B_255,C_254) != B_255
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_253,B_255)))
      | ~ v1_funct_2(C_254,A_253,B_255)
      | ~ v1_funct_1(C_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_4132,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_4126])).

tff(c_4142,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_70,c_4132])).

tff(c_4143,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4142])).

tff(c_28,plain,(
    ! [A_14] :
      ( k1_relat_1(k5_relat_1(A_14,k2_funct_1(A_14))) = k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4209,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4143,c_28])).

tff(c_4224,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_86,c_70,c_92,c_4209])).

tff(c_22,plain,(
    ! [A_13] :
      ( k2_relat_1(k2_funct_1(A_13)) = k1_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_220,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_229,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_220])).

tff(c_234,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_229])).

tff(c_197,plain,(
    ! [A_70] :
      ( k1_relat_1(k2_funct_1(A_70)) = k2_relat_1(A_70)
      | ~ v2_funct_1(A_70)
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_9] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_9)),A_9) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_90,plain,(
    ! [A_9] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_9)),A_9) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10])).

tff(c_1967,plain,(
    ! [A_151] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_151)),k2_funct_1(A_151)) = k2_funct_1(A_151)
      | ~ v1_relat_1(k2_funct_1(A_151))
      | ~ v2_funct_1(A_151)
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_90])).

tff(c_1988,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_1967])).

tff(c_2007,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_86,c_70,c_1988])).

tff(c_2010,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2007])).

tff(c_2013,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_2010])).

tff(c_2017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_86,c_2013])).

tff(c_2019,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2007])).

tff(c_18,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_88,plain,(
    ! [A_12] : v1_relat_1(k6_partfun1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_18])).

tff(c_2018,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2007])).

tff(c_12,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k6_relat_1(k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_89,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k6_partfun1(k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_12])).

tff(c_4,plain,(
    ! [A_1,B_5,C_7] :
      ( k5_relat_1(k5_relat_1(A_1,B_5),C_7) = k5_relat_1(A_1,k5_relat_1(B_5,C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2046,plain,(
    ! [C_7] :
      ( k5_relat_1(k6_partfun1('#skF_2'),k5_relat_1(k2_funct_1('#skF_3'),C_7)) = k5_relat_1(k2_funct_1('#skF_3'),C_7)
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k6_partfun1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2018,c_4])).

tff(c_2059,plain,(
    ! [C_158] :
      ( k5_relat_1(k6_partfun1('#skF_2'),k5_relat_1(k2_funct_1('#skF_3'),C_158)) = k5_relat_1(k2_funct_1('#skF_3'),C_158)
      | ~ v1_relat_1(C_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2019,c_2046])).

tff(c_2085,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_2059])).

tff(c_2097,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2019,c_88,c_2018,c_2085])).

tff(c_2117,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2097])).

tff(c_2136,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_86,c_70,c_2117])).

tff(c_4229,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4224,c_2136])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_232,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_220])).

tff(c_2544,plain,(
    ! [B_177,C_178,A_179] :
      ( k6_partfun1(B_177) = k5_relat_1(k2_funct_1(C_178),C_178)
      | k1_xboole_0 = B_177
      | ~ v2_funct_1(C_178)
      | k2_relset_1(A_179,B_177,C_178) != B_177
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_179,B_177)))
      | ~ v1_funct_2(C_178,A_179,B_177)
      | ~ v1_funct_1(C_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_2548,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_2544])).

tff(c_2556,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_232,c_2548])).

tff(c_2557,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2556])).

tff(c_2611,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2557])).

tff(c_44,plain,(
    ! [A_31] : m1_subset_1(k6_partfun1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_209,plain,(
    ! [A_71,B_72,D_73] :
      ( r2_relset_1(A_71,B_72,D_73,D_73)
      | ~ m1_subset_1(D_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_216,plain,(
    ! [A_31] : r2_relset_1(A_31,A_31,k6_partfun1(A_31),k6_partfun1(A_31)) ),
    inference(resolution,[status(thm)],[c_44,c_209])).

tff(c_1324,plain,(
    ! [D_127,F_124,C_125,E_122,A_126,B_123] :
      ( k1_partfun1(A_126,B_123,C_125,D_127,E_122,F_124) = k5_relat_1(E_122,F_124)
      | ~ m1_subset_1(F_124,k1_zfmisc_1(k2_zfmisc_1(C_125,D_127)))
      | ~ v1_funct_1(F_124)
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(A_126,B_123)))
      | ~ v1_funct_1(E_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1328,plain,(
    ! [A_126,B_123,E_122] :
      ( k1_partfun1(A_126,B_123,'#skF_2','#skF_1',E_122,'#skF_4') = k5_relat_1(E_122,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(A_126,B_123)))
      | ~ v1_funct_1(E_122) ) ),
    inference(resolution,[status(thm)],[c_76,c_1324])).

tff(c_1399,plain,(
    ! [A_131,B_132,E_133] :
      ( k1_partfun1(A_131,B_132,'#skF_2','#skF_1',E_133,'#skF_4') = k5_relat_1(E_133,'#skF_4')
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_1(E_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1328])).

tff(c_1408,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_1399])).

tff(c_1415,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1408])).

tff(c_72,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_486,plain,(
    ! [D_89,C_90,A_91,B_92] :
      ( D_89 = C_90
      | ~ r2_relset_1(A_91,B_92,C_90,D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_494,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_72,c_486])).

tff(c_509,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_494])).

tff(c_665,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_509])).

tff(c_1453,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1415,c_665])).

tff(c_1703,plain,(
    ! [A_143,C_144,D_142,F_145,E_147,B_146] :
      ( m1_subset_1(k1_partfun1(A_143,B_146,C_144,D_142,E_147,F_145),k1_zfmisc_1(k2_zfmisc_1(A_143,D_142)))
      | ~ m1_subset_1(F_145,k1_zfmisc_1(k2_zfmisc_1(C_144,D_142)))
      | ~ v1_funct_1(F_145)
      | ~ m1_subset_1(E_147,k1_zfmisc_1(k2_zfmisc_1(A_143,B_146)))
      | ~ v1_funct_1(E_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1731,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1415,c_1703])).

tff(c_1746,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_1731])).

tff(c_1748,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1453,c_1746])).

tff(c_1749,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_509])).

tff(c_3122,plain,(
    ! [A_206,B_207,C_208,D_209] :
      ( k2_relset_1(A_206,B_207,C_208) = B_207
      | ~ r2_relset_1(B_207,B_207,k1_partfun1(B_207,A_206,A_206,B_207,D_209,C_208),k6_partfun1(B_207))
      | ~ m1_subset_1(D_209,k1_zfmisc_1(k2_zfmisc_1(B_207,A_206)))
      | ~ v1_funct_2(D_209,B_207,A_206)
      | ~ v1_funct_1(D_209)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207)))
      | ~ v1_funct_2(C_208,A_206,B_207)
      | ~ v1_funct_1(C_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_3128,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1749,c_3122])).

tff(c_3132,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_86,c_84,c_82,c_216,c_232,c_3128])).

tff(c_3134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2611,c_3132])).

tff(c_3136,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2557])).

tff(c_3150,plain,
    ( k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3136,c_89])).

tff(c_3160,plain,(
    k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_3150])).

tff(c_3135,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2557])).

tff(c_3180,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3135])).

tff(c_20,plain,(
    ! [A_12] : v2_funct_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_87,plain,(
    ! [A_12] : v2_funct_1(k6_partfun1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_20])).

tff(c_3981,plain,(
    ! [C_245,D_244,E_247,A_248,B_246] :
      ( k1_xboole_0 = C_245
      | v2_funct_1(E_247)
      | k2_relset_1(A_248,B_246,D_244) != B_246
      | ~ v2_funct_1(k1_partfun1(A_248,B_246,B_246,C_245,D_244,E_247))
      | ~ m1_subset_1(E_247,k1_zfmisc_1(k2_zfmisc_1(B_246,C_245)))
      | ~ v1_funct_2(E_247,B_246,C_245)
      | ~ v1_funct_1(E_247)
      | ~ m1_subset_1(D_244,k1_zfmisc_1(k2_zfmisc_1(A_248,B_246)))
      | ~ v1_funct_2(D_244,A_248,B_246)
      | ~ v1_funct_1(D_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_3985,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1749,c_3981])).

tff(c_3990,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_78,c_76,c_87,c_74,c_3985])).

tff(c_3992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3180,c_68,c_3990])).

tff(c_3994,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3135])).

tff(c_3137,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3136,c_232])).

tff(c_4130,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_4126])).

tff(c_4138,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_3137,c_3994,c_4130])).

tff(c_4139,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4138])).

tff(c_4153,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4139,c_28])).

tff(c_4164,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_80,c_3994,c_92,c_4153])).

tff(c_285,plain,(
    ! [A_81,B_82,C_83] :
      ( k5_relat_1(k5_relat_1(A_81,B_82),C_83) = k5_relat_1(A_81,k5_relat_1(B_82,C_83))
      | ~ v1_relat_1(C_83)
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_325,plain,(
    ! [A_9,C_83] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_9)),k5_relat_1(A_9,C_83)) = k5_relat_1(A_9,C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_relat_1(A_9)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_9)))
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_285])).

tff(c_510,plain,(
    ! [A_93,C_94] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_93)),k5_relat_1(A_93,C_94)) = k5_relat_1(A_93,C_94)
      | ~ v1_relat_1(C_94)
      | ~ v1_relat_1(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_325])).

tff(c_552,plain,(
    ! [A_10] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_10)),A_10) = k5_relat_1(A_10,k6_partfun1(k2_relat_1(A_10)))
      | ~ v1_relat_1(k6_partfun1(k2_relat_1(A_10)))
      | ~ v1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_510])).

tff(c_578,plain,(
    ! [A_10] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_10)),A_10) = k5_relat_1(A_10,k6_partfun1(k2_relat_1(A_10)))
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_552])).

tff(c_4175,plain,
    ( k5_relat_1('#skF_4',k6_partfun1(k2_relat_1('#skF_4'))) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4164,c_578])).

tff(c_4187,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_3160,c_3136,c_4175])).

tff(c_2223,plain,(
    ! [C_165,E_162,B_163,A_166,D_167,F_164] :
      ( k1_partfun1(A_166,B_163,C_165,D_167,E_162,F_164) = k5_relat_1(E_162,F_164)
      | ~ m1_subset_1(F_164,k1_zfmisc_1(k2_zfmisc_1(C_165,D_167)))
      | ~ v1_funct_1(F_164)
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_166,B_163)))
      | ~ v1_funct_1(E_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2227,plain,(
    ! [A_166,B_163,E_162] :
      ( k1_partfun1(A_166,B_163,'#skF_2','#skF_1',E_162,'#skF_4') = k5_relat_1(E_162,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_166,B_163)))
      | ~ v1_funct_1(E_162) ) ),
    inference(resolution,[status(thm)],[c_76,c_2223])).

tff(c_4363,plain,(
    ! [A_262,B_263,E_264] :
      ( k1_partfun1(A_262,B_263,'#skF_2','#skF_1',E_264,'#skF_4') = k5_relat_1(E_264,'#skF_4')
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(A_262,B_263)))
      | ~ v1_funct_1(E_264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2227])).

tff(c_4375,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_4363])).

tff(c_4383,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1749,c_4375])).

tff(c_2550,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_2544])).

tff(c_2560,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_70,c_2550])).

tff(c_2561,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2560])).

tff(c_2574,plain,(
    ! [C_7] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_7)) = k5_relat_1(k6_partfun1('#skF_2'),C_7)
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2561,c_4])).

tff(c_5039,plain,(
    ! [C_291] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_291)) = k5_relat_1(k6_partfun1('#skF_2'),C_291)
      | ~ v1_relat_1(C_291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2019,c_147,c_2574])).

tff(c_5069,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4383,c_5039])).

tff(c_5096,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_4229,c_4187,c_5069])).

tff(c_5098,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5096])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:01:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.58/2.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.58/2.35  
% 6.58/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.58/2.35  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.58/2.35  
% 6.58/2.35  %Foreground sorts:
% 6.58/2.35  
% 6.58/2.35  
% 6.58/2.35  %Background operators:
% 6.58/2.35  
% 6.58/2.35  
% 6.58/2.35  %Foreground operators:
% 6.58/2.35  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.58/2.35  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 6.58/2.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.58/2.35  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.58/2.35  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.58/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.58/2.35  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.58/2.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.58/2.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.58/2.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.58/2.35  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.58/2.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.58/2.35  tff('#skF_2', type, '#skF_2': $i).
% 6.58/2.35  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.58/2.35  tff('#skF_3', type, '#skF_3': $i).
% 6.58/2.35  tff('#skF_1', type, '#skF_1': $i).
% 6.58/2.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.58/2.35  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.58/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.58/2.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.58/2.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.58/2.35  tff('#skF_4', type, '#skF_4': $i).
% 6.58/2.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.58/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.58/2.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.58/2.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.58/2.35  
% 6.92/2.38  tff(f_209, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 6.92/2.38  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.92/2.38  tff(f_124, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.92/2.38  tff(f_40, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.92/2.38  tff(f_183, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 6.92/2.38  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 6.92/2.38  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 6.92/2.38  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.92/2.38  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.92/2.38  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 6.92/2.38  tff(f_60, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.92/2.38  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 6.92/2.38  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 6.92/2.38  tff(f_112, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.92/2.38  tff(f_96, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.92/2.38  tff(f_122, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.92/2.38  tff(f_108, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.92/2.38  tff(f_141, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 6.92/2.38  tff(f_167, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 6.92/2.38  tff(c_64, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.92/2.38  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.92/2.38  tff(c_134, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.92/2.38  tff(c_146, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_134])).
% 6.92/2.38  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.92/2.38  tff(c_147, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_134])).
% 6.92/2.38  tff(c_86, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.92/2.38  tff(c_70, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.92/2.38  tff(c_48, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.92/2.38  tff(c_6, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.92/2.38  tff(c_92, plain, (![A_8]: (k1_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6])).
% 6.92/2.38  tff(c_66, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.92/2.38  tff(c_84, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.92/2.38  tff(c_74, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.92/2.38  tff(c_4126, plain, (![A_253, C_254, B_255]: (k6_partfun1(A_253)=k5_relat_1(C_254, k2_funct_1(C_254)) | k1_xboole_0=B_255 | ~v2_funct_1(C_254) | k2_relset_1(A_253, B_255, C_254)!=B_255 | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_253, B_255))) | ~v1_funct_2(C_254, A_253, B_255) | ~v1_funct_1(C_254))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.92/2.38  tff(c_4132, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_4126])).
% 6.92/2.38  tff(c_4142, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_70, c_4132])).
% 6.92/2.38  tff(c_4143, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_4142])).
% 6.92/2.38  tff(c_28, plain, (![A_14]: (k1_relat_1(k5_relat_1(A_14, k2_funct_1(A_14)))=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.92/2.38  tff(c_4209, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4143, c_28])).
% 6.92/2.38  tff(c_4224, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_147, c_86, c_70, c_92, c_4209])).
% 6.92/2.38  tff(c_22, plain, (![A_13]: (k2_relat_1(k2_funct_1(A_13))=k1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.92/2.38  tff(c_16, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.92/2.38  tff(c_220, plain, (![A_75, B_76, C_77]: (k2_relset_1(A_75, B_76, C_77)=k2_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.92/2.38  tff(c_229, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_220])).
% 6.92/2.38  tff(c_234, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_229])).
% 6.92/2.38  tff(c_197, plain, (![A_70]: (k1_relat_1(k2_funct_1(A_70))=k2_relat_1(A_70) | ~v2_funct_1(A_70) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.92/2.38  tff(c_10, plain, (![A_9]: (k5_relat_1(k6_relat_1(k1_relat_1(A_9)), A_9)=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.92/2.38  tff(c_90, plain, (![A_9]: (k5_relat_1(k6_partfun1(k1_relat_1(A_9)), A_9)=A_9 | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10])).
% 6.92/2.38  tff(c_1967, plain, (![A_151]: (k5_relat_1(k6_partfun1(k2_relat_1(A_151)), k2_funct_1(A_151))=k2_funct_1(A_151) | ~v1_relat_1(k2_funct_1(A_151)) | ~v2_funct_1(A_151) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151))), inference(superposition, [status(thm), theory('equality')], [c_197, c_90])).
% 6.92/2.38  tff(c_1988, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_234, c_1967])).
% 6.92/2.38  tff(c_2007, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_86, c_70, c_1988])).
% 6.92/2.38  tff(c_2010, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2007])).
% 6.92/2.38  tff(c_2013, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_2010])).
% 6.92/2.38  tff(c_2017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_147, c_86, c_2013])).
% 6.92/2.38  tff(c_2019, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2007])).
% 6.92/2.38  tff(c_18, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.92/2.38  tff(c_88, plain, (![A_12]: (v1_relat_1(k6_partfun1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_18])).
% 6.92/2.38  tff(c_2018, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_2007])).
% 6.92/2.38  tff(c_12, plain, (![A_10]: (k5_relat_1(A_10, k6_relat_1(k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.92/2.38  tff(c_89, plain, (![A_10]: (k5_relat_1(A_10, k6_partfun1(k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_12])).
% 6.92/2.38  tff(c_4, plain, (![A_1, B_5, C_7]: (k5_relat_1(k5_relat_1(A_1, B_5), C_7)=k5_relat_1(A_1, k5_relat_1(B_5, C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1(B_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.92/2.38  tff(c_2046, plain, (![C_7]: (k5_relat_1(k6_partfun1('#skF_2'), k5_relat_1(k2_funct_1('#skF_3'), C_7))=k5_relat_1(k2_funct_1('#skF_3'), C_7) | ~v1_relat_1(C_7) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k6_partfun1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2018, c_4])).
% 6.92/2.38  tff(c_2059, plain, (![C_158]: (k5_relat_1(k6_partfun1('#skF_2'), k5_relat_1(k2_funct_1('#skF_3'), C_158))=k5_relat_1(k2_funct_1('#skF_3'), C_158) | ~v1_relat_1(C_158))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2019, c_2046])).
% 6.92/2.38  tff(c_2085, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3')) | ~v1_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_2059])).
% 6.92/2.38  tff(c_2097, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2019, c_88, c_2018, c_2085])).
% 6.92/2.38  tff(c_2117, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_2097])).
% 6.92/2.38  tff(c_2136, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_86, c_70, c_2117])).
% 6.92/2.38  tff(c_4229, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4224, c_2136])).
% 6.92/2.38  tff(c_68, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.92/2.38  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.92/2.38  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.92/2.38  tff(c_232, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_220])).
% 6.92/2.38  tff(c_2544, plain, (![B_177, C_178, A_179]: (k6_partfun1(B_177)=k5_relat_1(k2_funct_1(C_178), C_178) | k1_xboole_0=B_177 | ~v2_funct_1(C_178) | k2_relset_1(A_179, B_177, C_178)!=B_177 | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_179, B_177))) | ~v1_funct_2(C_178, A_179, B_177) | ~v1_funct_1(C_178))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.92/2.38  tff(c_2548, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_2544])).
% 6.92/2.38  tff(c_2556, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_232, c_2548])).
% 6.92/2.38  tff(c_2557, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_68, c_2556])).
% 6.92/2.38  tff(c_2611, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2557])).
% 6.92/2.38  tff(c_44, plain, (![A_31]: (m1_subset_1(k6_partfun1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.92/2.38  tff(c_209, plain, (![A_71, B_72, D_73]: (r2_relset_1(A_71, B_72, D_73, D_73) | ~m1_subset_1(D_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.92/2.38  tff(c_216, plain, (![A_31]: (r2_relset_1(A_31, A_31, k6_partfun1(A_31), k6_partfun1(A_31)))), inference(resolution, [status(thm)], [c_44, c_209])).
% 6.92/2.38  tff(c_1324, plain, (![D_127, F_124, C_125, E_122, A_126, B_123]: (k1_partfun1(A_126, B_123, C_125, D_127, E_122, F_124)=k5_relat_1(E_122, F_124) | ~m1_subset_1(F_124, k1_zfmisc_1(k2_zfmisc_1(C_125, D_127))) | ~v1_funct_1(F_124) | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(A_126, B_123))) | ~v1_funct_1(E_122))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.92/2.38  tff(c_1328, plain, (![A_126, B_123, E_122]: (k1_partfun1(A_126, B_123, '#skF_2', '#skF_1', E_122, '#skF_4')=k5_relat_1(E_122, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(A_126, B_123))) | ~v1_funct_1(E_122))), inference(resolution, [status(thm)], [c_76, c_1324])).
% 6.92/2.38  tff(c_1399, plain, (![A_131, B_132, E_133]: (k1_partfun1(A_131, B_132, '#skF_2', '#skF_1', E_133, '#skF_4')=k5_relat_1(E_133, '#skF_4') | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~v1_funct_1(E_133))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1328])).
% 6.92/2.38  tff(c_1408, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_1399])).
% 6.92/2.38  tff(c_1415, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1408])).
% 6.92/2.38  tff(c_72, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.92/2.38  tff(c_486, plain, (![D_89, C_90, A_91, B_92]: (D_89=C_90 | ~r2_relset_1(A_91, B_92, C_90, D_89) | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.92/2.38  tff(c_494, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_72, c_486])).
% 6.92/2.38  tff(c_509, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_494])).
% 6.92/2.38  tff(c_665, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_509])).
% 6.92/2.38  tff(c_1453, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1415, c_665])).
% 6.92/2.38  tff(c_1703, plain, (![A_143, C_144, D_142, F_145, E_147, B_146]: (m1_subset_1(k1_partfun1(A_143, B_146, C_144, D_142, E_147, F_145), k1_zfmisc_1(k2_zfmisc_1(A_143, D_142))) | ~m1_subset_1(F_145, k1_zfmisc_1(k2_zfmisc_1(C_144, D_142))) | ~v1_funct_1(F_145) | ~m1_subset_1(E_147, k1_zfmisc_1(k2_zfmisc_1(A_143, B_146))) | ~v1_funct_1(E_147))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.92/2.38  tff(c_1731, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1415, c_1703])).
% 6.92/2.38  tff(c_1746, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_1731])).
% 6.92/2.38  tff(c_1748, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1453, c_1746])).
% 6.92/2.38  tff(c_1749, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_509])).
% 6.92/2.38  tff(c_3122, plain, (![A_206, B_207, C_208, D_209]: (k2_relset_1(A_206, B_207, C_208)=B_207 | ~r2_relset_1(B_207, B_207, k1_partfun1(B_207, A_206, A_206, B_207, D_209, C_208), k6_partfun1(B_207)) | ~m1_subset_1(D_209, k1_zfmisc_1(k2_zfmisc_1(B_207, A_206))) | ~v1_funct_2(D_209, B_207, A_206) | ~v1_funct_1(D_209) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))) | ~v1_funct_2(C_208, A_206, B_207) | ~v1_funct_1(C_208))), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.92/2.38  tff(c_3128, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1749, c_3122])).
% 6.92/2.38  tff(c_3132, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_86, c_84, c_82, c_216, c_232, c_3128])).
% 6.92/2.38  tff(c_3134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2611, c_3132])).
% 6.92/2.38  tff(c_3136, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_2557])).
% 6.92/2.38  tff(c_3150, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3136, c_89])).
% 6.92/2.38  tff(c_3160, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_3150])).
% 6.92/2.38  tff(c_3135, plain, (~v2_funct_1('#skF_4') | k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2557])).
% 6.92/2.38  tff(c_3180, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_3135])).
% 6.92/2.38  tff(c_20, plain, (![A_12]: (v2_funct_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.92/2.38  tff(c_87, plain, (![A_12]: (v2_funct_1(k6_partfun1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_20])).
% 6.92/2.38  tff(c_3981, plain, (![C_245, D_244, E_247, A_248, B_246]: (k1_xboole_0=C_245 | v2_funct_1(E_247) | k2_relset_1(A_248, B_246, D_244)!=B_246 | ~v2_funct_1(k1_partfun1(A_248, B_246, B_246, C_245, D_244, E_247)) | ~m1_subset_1(E_247, k1_zfmisc_1(k2_zfmisc_1(B_246, C_245))) | ~v1_funct_2(E_247, B_246, C_245) | ~v1_funct_1(E_247) | ~m1_subset_1(D_244, k1_zfmisc_1(k2_zfmisc_1(A_248, B_246))) | ~v1_funct_2(D_244, A_248, B_246) | ~v1_funct_1(D_244))), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.92/2.38  tff(c_3985, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1749, c_3981])).
% 6.92/2.38  tff(c_3990, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_78, c_76, c_87, c_74, c_3985])).
% 6.92/2.38  tff(c_3992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3180, c_68, c_3990])).
% 6.92/2.38  tff(c_3994, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_3135])).
% 6.92/2.38  tff(c_3137, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3136, c_232])).
% 6.92/2.38  tff(c_4130, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_4126])).
% 6.92/2.38  tff(c_4138, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_3137, c_3994, c_4130])).
% 6.92/2.38  tff(c_4139, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_4138])).
% 6.92/2.38  tff(c_4153, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4139, c_28])).
% 6.92/2.38  tff(c_4164, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_80, c_3994, c_92, c_4153])).
% 6.92/2.38  tff(c_285, plain, (![A_81, B_82, C_83]: (k5_relat_1(k5_relat_1(A_81, B_82), C_83)=k5_relat_1(A_81, k5_relat_1(B_82, C_83)) | ~v1_relat_1(C_83) | ~v1_relat_1(B_82) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.92/2.38  tff(c_325, plain, (![A_9, C_83]: (k5_relat_1(k6_partfun1(k1_relat_1(A_9)), k5_relat_1(A_9, C_83))=k5_relat_1(A_9, C_83) | ~v1_relat_1(C_83) | ~v1_relat_1(A_9) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_9))) | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_90, c_285])).
% 6.92/2.38  tff(c_510, plain, (![A_93, C_94]: (k5_relat_1(k6_partfun1(k1_relat_1(A_93)), k5_relat_1(A_93, C_94))=k5_relat_1(A_93, C_94) | ~v1_relat_1(C_94) | ~v1_relat_1(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_325])).
% 6.92/2.38  tff(c_552, plain, (![A_10]: (k5_relat_1(k6_partfun1(k1_relat_1(A_10)), A_10)=k5_relat_1(A_10, k6_partfun1(k2_relat_1(A_10))) | ~v1_relat_1(k6_partfun1(k2_relat_1(A_10))) | ~v1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_89, c_510])).
% 6.92/2.38  tff(c_578, plain, (![A_10]: (k5_relat_1(k6_partfun1(k1_relat_1(A_10)), A_10)=k5_relat_1(A_10, k6_partfun1(k2_relat_1(A_10))) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_552])).
% 6.92/2.38  tff(c_4175, plain, (k5_relat_1('#skF_4', k6_partfun1(k2_relat_1('#skF_4')))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4164, c_578])).
% 6.92/2.38  tff(c_4187, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_3160, c_3136, c_4175])).
% 6.92/2.38  tff(c_2223, plain, (![C_165, E_162, B_163, A_166, D_167, F_164]: (k1_partfun1(A_166, B_163, C_165, D_167, E_162, F_164)=k5_relat_1(E_162, F_164) | ~m1_subset_1(F_164, k1_zfmisc_1(k2_zfmisc_1(C_165, D_167))) | ~v1_funct_1(F_164) | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(A_166, B_163))) | ~v1_funct_1(E_162))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.92/2.38  tff(c_2227, plain, (![A_166, B_163, E_162]: (k1_partfun1(A_166, B_163, '#skF_2', '#skF_1', E_162, '#skF_4')=k5_relat_1(E_162, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(A_166, B_163))) | ~v1_funct_1(E_162))), inference(resolution, [status(thm)], [c_76, c_2223])).
% 6.92/2.38  tff(c_4363, plain, (![A_262, B_263, E_264]: (k1_partfun1(A_262, B_263, '#skF_2', '#skF_1', E_264, '#skF_4')=k5_relat_1(E_264, '#skF_4') | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(A_262, B_263))) | ~v1_funct_1(E_264))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2227])).
% 6.92/2.38  tff(c_4375, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_4363])).
% 6.92/2.38  tff(c_4383, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1749, c_4375])).
% 6.92/2.38  tff(c_2550, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_2544])).
% 6.92/2.38  tff(c_2560, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_70, c_2550])).
% 6.92/2.38  tff(c_2561, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_66, c_2560])).
% 6.92/2.38  tff(c_2574, plain, (![C_7]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_7))=k5_relat_1(k6_partfun1('#skF_2'), C_7) | ~v1_relat_1(C_7) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2561, c_4])).
% 6.92/2.38  tff(c_5039, plain, (![C_291]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_291))=k5_relat_1(k6_partfun1('#skF_2'), C_291) | ~v1_relat_1(C_291))), inference(demodulation, [status(thm), theory('equality')], [c_2019, c_147, c_2574])).
% 6.92/2.38  tff(c_5069, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4383, c_5039])).
% 6.92/2.38  tff(c_5096, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_4229, c_4187, c_5069])).
% 6.92/2.38  tff(c_5098, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_5096])).
% 6.92/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.92/2.38  
% 6.92/2.38  Inference rules
% 6.92/2.38  ----------------------
% 6.92/2.38  #Ref     : 0
% 6.92/2.38  #Sup     : 1080
% 6.92/2.38  #Fact    : 0
% 6.92/2.38  #Define  : 0
% 6.92/2.38  #Split   : 12
% 6.92/2.38  #Chain   : 0
% 6.92/2.38  #Close   : 0
% 6.92/2.38  
% 6.92/2.38  Ordering : KBO
% 6.92/2.38  
% 6.92/2.38  Simplification rules
% 6.92/2.38  ----------------------
% 6.92/2.38  #Subsume      : 43
% 6.92/2.38  #Demod        : 1604
% 6.92/2.38  #Tautology    : 598
% 6.92/2.38  #SimpNegUnit  : 37
% 6.92/2.38  #BackRed      : 33
% 6.92/2.38  
% 6.92/2.38  #Partial instantiations: 0
% 6.92/2.38  #Strategies tried      : 1
% 6.92/2.38  
% 6.92/2.38  Timing (in seconds)
% 6.92/2.38  ----------------------
% 6.92/2.38  Preprocessing        : 0.40
% 6.92/2.38  Parsing              : 0.22
% 6.92/2.38  CNF conversion       : 0.03
% 6.92/2.38  Main loop            : 1.14
% 6.92/2.38  Inferencing          : 0.39
% 6.92/2.38  Reduction            : 0.45
% 6.92/2.39  Demodulation         : 0.34
% 6.92/2.39  BG Simplification    : 0.05
% 6.92/2.39  Subsumption          : 0.18
% 6.92/2.39  Abstraction          : 0.06
% 6.92/2.39  MUC search           : 0.00
% 6.92/2.39  Cooper               : 0.00
% 6.92/2.39  Total                : 1.60
% 6.92/2.39  Index Insertion      : 0.00
% 6.92/2.39  Index Deletion       : 0.00
% 6.92/2.39  Index Matching       : 0.00
% 6.92/2.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
