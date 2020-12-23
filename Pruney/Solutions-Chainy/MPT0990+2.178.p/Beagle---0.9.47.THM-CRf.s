%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:22 EST 2020

% Result     : Theorem 5.93s
% Output     : CNFRefutation 6.17s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 461 expanded)
%              Number of leaves         :   46 ( 184 expanded)
%              Depth                    :   12
%              Number of atoms          :  326 (1857 expanded)
%              Number of equality atoms :  106 ( 576 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_217,negated_conjecture,(
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

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_132,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_58,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_191,axiom,(
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

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_120,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_130,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_116,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_149,axiom,(
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

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_175,axiom,(
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

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_66,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_6,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_178,plain,(
    ! [B_71,A_72] :
      ( v1_relat_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_184,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_78,c_178])).

tff(c_193,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_184])).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_187,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_84,c_178])).

tff(c_196,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_187])).

tff(c_88,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_72,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_214,plain,(
    ! [A_74] :
      ( k4_relat_1(A_74) = k2_funct_1(A_74)
      | ~ v2_funct_1(A_74)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_220,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_214])).

tff(c_226,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_88,c_220])).

tff(c_4,plain,(
    ! [A_4] :
      ( v1_relat_1(k4_relat_1(A_4))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_236,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_4])).

tff(c_244,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_236])).

tff(c_50,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_14,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_94,plain,(
    ! [A_15] : k1_relat_1(k6_partfun1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_14])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_86,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_76,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_1915,plain,(
    ! [A_163,C_164,B_165] :
      ( k6_partfun1(A_163) = k5_relat_1(C_164,k2_funct_1(C_164))
      | k1_xboole_0 = B_165
      | ~ v2_funct_1(C_164)
      | k2_relset_1(A_163,B_165,C_164) != B_165
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_163,B_165)))
      | ~ v1_funct_2(C_164,A_163,B_165)
      | ~ v1_funct_1(C_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1921,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_1915])).

tff(c_1931,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_76,c_72,c_1921])).

tff(c_1932,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1931])).

tff(c_34,plain,(
    ! [A_21] :
      ( k1_relat_1(k5_relat_1(A_21,k2_funct_1(A_21))) = k1_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1942,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1932,c_34])).

tff(c_1953,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_88,c_72,c_94,c_1942])).

tff(c_8,plain,(
    ! [A_7] :
      ( k2_relat_1(k4_relat_1(A_7)) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20,plain,(
    ! [A_17] :
      ( k5_relat_1(A_17,k6_relat_1(k2_relat_1(A_17))) = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_197,plain,(
    ! [A_73] :
      ( k5_relat_1(A_73,k6_partfun1(k2_relat_1(A_73))) = A_73
      | ~ v1_relat_1(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_20])).

tff(c_206,plain,(
    ! [A_7] :
      ( k5_relat_1(k4_relat_1(A_7),k6_partfun1(k1_relat_1(A_7))) = k4_relat_1(A_7)
      | ~ v1_relat_1(k4_relat_1(A_7))
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_197])).

tff(c_1970,plain,
    ( k5_relat_1(k4_relat_1('#skF_3'),k6_partfun1('#skF_1')) = k4_relat_1('#skF_3')
    | ~ v1_relat_1(k4_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1953,c_206])).

tff(c_1981,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_244,c_226,c_226,c_226,c_1970])).

tff(c_82,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_80,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_1919,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_1915])).

tff(c_1927,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_1919])).

tff(c_1928,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1927])).

tff(c_1986,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1928])).

tff(c_46,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_255,plain,(
    ! [A_75,B_76,D_77] :
      ( r2_relset_1(A_75,B_76,D_77,D_77)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_262,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_46,c_255])).

tff(c_1073,plain,(
    ! [A_112,D_116,C_114,F_115,E_113,B_117] :
      ( k1_partfun1(A_112,B_117,C_114,D_116,E_113,F_115) = k5_relat_1(E_113,F_115)
      | ~ m1_subset_1(F_115,k1_zfmisc_1(k2_zfmisc_1(C_114,D_116)))
      | ~ v1_funct_1(F_115)
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(A_112,B_117)))
      | ~ v1_funct_1(E_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1077,plain,(
    ! [A_112,B_117,E_113] :
      ( k1_partfun1(A_112,B_117,'#skF_2','#skF_1',E_113,'#skF_4') = k5_relat_1(E_113,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(A_112,B_117)))
      | ~ v1_funct_1(E_113) ) ),
    inference(resolution,[status(thm)],[c_78,c_1073])).

tff(c_1104,plain,(
    ! [A_121,B_122,E_123] :
      ( k1_partfun1(A_121,B_122,'#skF_2','#skF_1',E_123,'#skF_4') = k5_relat_1(E_123,'#skF_4')
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ v1_funct_1(E_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1077])).

tff(c_1113,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_1104])).

tff(c_1120,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1113])).

tff(c_74,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_540,plain,(
    ! [D_91,C_92,A_93,B_94] :
      ( D_91 = C_92
      | ~ r2_relset_1(A_93,B_94,C_92,D_91)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_548,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_74,c_540])).

tff(c_563,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_548])).

tff(c_800,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_563])).

tff(c_1127,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1120,c_800])).

tff(c_1423,plain,(
    ! [E_140,F_138,B_136,A_137,C_139,D_135] :
      ( m1_subset_1(k1_partfun1(A_137,B_136,C_139,D_135,E_140,F_138),k1_zfmisc_1(k2_zfmisc_1(A_137,D_135)))
      | ~ m1_subset_1(F_138,k1_zfmisc_1(k2_zfmisc_1(C_139,D_135)))
      | ~ v1_funct_1(F_138)
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_137,B_136)))
      | ~ v1_funct_1(E_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1451,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1120,c_1423])).

tff(c_1468,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_82,c_78,c_1451])).

tff(c_1470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1127,c_1468])).

tff(c_1471,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_563])).

tff(c_2527,plain,(
    ! [A_189,B_190,C_191,D_192] :
      ( k2_relset_1(A_189,B_190,C_191) = B_190
      | ~ r2_relset_1(B_190,B_190,k1_partfun1(B_190,A_189,A_189,B_190,D_192,C_191),k6_partfun1(B_190))
      | ~ m1_subset_1(D_192,k1_zfmisc_1(k2_zfmisc_1(B_190,A_189)))
      | ~ v1_funct_2(D_192,B_190,A_189)
      | ~ v1_funct_1(D_192)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190)))
      | ~ v1_funct_2(C_191,A_189,B_190)
      | ~ v1_funct_1(C_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2533,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1471,c_2527])).

tff(c_2537,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_88,c_86,c_84,c_262,c_2533])).

tff(c_2539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1986,c_2537])).

tff(c_2540,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1928])).

tff(c_2584,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2540])).

tff(c_30,plain,(
    ! [A_20] : v2_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_89,plain,(
    ! [A_20] : v2_funct_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_30])).

tff(c_3324,plain,(
    ! [C_226,B_222,A_223,D_225,E_224] :
      ( k1_xboole_0 = C_226
      | v2_funct_1(E_224)
      | k2_relset_1(A_223,B_222,D_225) != B_222
      | ~ v2_funct_1(k1_partfun1(A_223,B_222,B_222,C_226,D_225,E_224))
      | ~ m1_subset_1(E_224,k1_zfmisc_1(k2_zfmisc_1(B_222,C_226)))
      | ~ v1_funct_2(E_224,B_222,C_226)
      | ~ v1_funct_1(E_224)
      | ~ m1_subset_1(D_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_222)))
      | ~ v1_funct_2(D_225,A_223,B_222)
      | ~ v1_funct_1(D_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_3328,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1471,c_3324])).

tff(c_3333,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_82,c_80,c_78,c_89,c_76,c_3328])).

tff(c_3335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2584,c_70,c_3333])).

tff(c_3337,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2540])).

tff(c_3336,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2540])).

tff(c_3442,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3336,c_34])).

tff(c_3453,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_82,c_3337,c_94,c_3442])).

tff(c_18,plain,(
    ! [A_16] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_16)),A_16) = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_92,plain,(
    ! [A_16] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_16)),A_16) = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_18])).

tff(c_3470,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3453,c_92])).

tff(c_3480,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_3470])).

tff(c_1835,plain,(
    ! [A_152,C_154,D_156,F_155,E_153,B_157] :
      ( k1_partfun1(A_152,B_157,C_154,D_156,E_153,F_155) = k5_relat_1(E_153,F_155)
      | ~ m1_subset_1(F_155,k1_zfmisc_1(k2_zfmisc_1(C_154,D_156)))
      | ~ v1_funct_1(F_155)
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_152,B_157)))
      | ~ v1_funct_1(E_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1839,plain,(
    ! [A_152,B_157,E_153] :
      ( k1_partfun1(A_152,B_157,'#skF_2','#skF_1',E_153,'#skF_4') = k5_relat_1(E_153,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_152,B_157)))
      | ~ v1_funct_1(E_153) ) ),
    inference(resolution,[status(thm)],[c_78,c_1835])).

tff(c_4356,plain,(
    ! [A_267,B_268,E_269] :
      ( k1_partfun1(A_267,B_268,'#skF_2','#skF_1',E_269,'#skF_4') = k5_relat_1(E_269,'#skF_4')
      | ~ m1_subset_1(E_269,k1_zfmisc_1(k2_zfmisc_1(A_267,B_268)))
      | ~ v1_funct_1(E_269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1839])).

tff(c_4374,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_4356])).

tff(c_4388,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1471,c_4374])).

tff(c_3483,plain,(
    ! [B_230,C_231,A_232] :
      ( k6_partfun1(B_230) = k5_relat_1(k2_funct_1(C_231),C_231)
      | k1_xboole_0 = B_230
      | ~ v2_funct_1(C_231)
      | k2_relset_1(A_232,B_230,C_231) != B_230
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_232,B_230)))
      | ~ v1_funct_2(C_231,A_232,B_230)
      | ~ v1_funct_1(C_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_3489,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_3483])).

tff(c_3499,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_76,c_72,c_3489])).

tff(c_3500,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3499])).

tff(c_12,plain,(
    ! [A_8,B_12,C_14] :
      ( k5_relat_1(k5_relat_1(A_8,B_12),C_14) = k5_relat_1(A_8,k5_relat_1(B_12,C_14))
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3563,plain,(
    ! [C_14] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_14)) = k5_relat_1(k6_partfun1('#skF_2'),C_14)
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3500,c_12])).

tff(c_3571,plain,(
    ! [C_14] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_14)) = k5_relat_1(k6_partfun1('#skF_2'),C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_196,c_3563])).

tff(c_4392,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4388,c_3571])).

tff(c_4405,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_1981,c_3480,c_4392])).

tff(c_4407,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4405])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:19:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.93/2.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.16  
% 5.93/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.16  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.93/2.16  
% 5.93/2.16  %Foreground sorts:
% 5.93/2.16  
% 5.93/2.16  
% 5.93/2.16  %Background operators:
% 5.93/2.16  
% 5.93/2.16  
% 5.93/2.16  %Foreground operators:
% 5.93/2.16  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.93/2.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.93/2.16  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.93/2.16  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.93/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.93/2.16  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.93/2.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.93/2.16  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.93/2.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.93/2.16  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.93/2.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.93/2.16  tff('#skF_2', type, '#skF_2': $i).
% 5.93/2.16  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.93/2.16  tff('#skF_3', type, '#skF_3': $i).
% 5.93/2.16  tff('#skF_1', type, '#skF_1': $i).
% 5.93/2.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.93/2.16  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.93/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.93/2.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.93/2.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.93/2.16  tff('#skF_4', type, '#skF_4': $i).
% 5.93/2.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.93/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.93/2.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.93/2.16  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.93/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.93/2.16  
% 6.17/2.19  tff(f_217, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 6.17/2.19  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.17/2.19  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.17/2.19  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 6.17/2.19  tff(f_36, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 6.17/2.19  tff(f_132, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.17/2.19  tff(f_58, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 6.17/2.19  tff(f_191, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 6.17/2.19  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 6.17/2.19  tff(f_44, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 6.17/2.19  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 6.17/2.19  tff(f_120, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.17/2.19  tff(f_104, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.17/2.19  tff(f_130, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.17/2.19  tff(f_116, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.17/2.19  tff(f_149, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 6.17/2.19  tff(f_86, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.17/2.19  tff(f_175, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 6.17/2.19  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 6.17/2.19  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 6.17/2.19  tff(c_66, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_217])).
% 6.17/2.19  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.17/2.19  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_217])).
% 6.17/2.19  tff(c_178, plain, (![B_71, A_72]: (v1_relat_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.17/2.19  tff(c_184, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_78, c_178])).
% 6.17/2.19  tff(c_193, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_184])).
% 6.17/2.19  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_217])).
% 6.17/2.19  tff(c_187, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_84, c_178])).
% 6.17/2.19  tff(c_196, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_187])).
% 6.17/2.19  tff(c_88, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_217])).
% 6.17/2.19  tff(c_72, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_217])).
% 6.17/2.19  tff(c_214, plain, (![A_74]: (k4_relat_1(A_74)=k2_funct_1(A_74) | ~v2_funct_1(A_74) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.17/2.19  tff(c_220, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_214])).
% 6.17/2.19  tff(c_226, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_88, c_220])).
% 6.17/2.19  tff(c_4, plain, (![A_4]: (v1_relat_1(k4_relat_1(A_4)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.17/2.19  tff(c_236, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_226, c_4])).
% 6.17/2.19  tff(c_244, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_236])).
% 6.17/2.19  tff(c_50, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.17/2.19  tff(c_14, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.17/2.19  tff(c_94, plain, (![A_15]: (k1_relat_1(k6_partfun1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_14])).
% 6.17/2.19  tff(c_68, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_217])).
% 6.17/2.19  tff(c_86, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_217])).
% 6.17/2.19  tff(c_76, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_217])).
% 6.17/2.19  tff(c_1915, plain, (![A_163, C_164, B_165]: (k6_partfun1(A_163)=k5_relat_1(C_164, k2_funct_1(C_164)) | k1_xboole_0=B_165 | ~v2_funct_1(C_164) | k2_relset_1(A_163, B_165, C_164)!=B_165 | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_163, B_165))) | ~v1_funct_2(C_164, A_163, B_165) | ~v1_funct_1(C_164))), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.17/2.19  tff(c_1921, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_1915])).
% 6.17/2.19  tff(c_1931, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_76, c_72, c_1921])).
% 6.17/2.19  tff(c_1932, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_1931])).
% 6.17/2.19  tff(c_34, plain, (![A_21]: (k1_relat_1(k5_relat_1(A_21, k2_funct_1(A_21)))=k1_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.17/2.19  tff(c_1942, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1932, c_34])).
% 6.17/2.19  tff(c_1953, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_88, c_72, c_94, c_1942])).
% 6.17/2.19  tff(c_8, plain, (![A_7]: (k2_relat_1(k4_relat_1(A_7))=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.17/2.19  tff(c_20, plain, (![A_17]: (k5_relat_1(A_17, k6_relat_1(k2_relat_1(A_17)))=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.17/2.19  tff(c_197, plain, (![A_73]: (k5_relat_1(A_73, k6_partfun1(k2_relat_1(A_73)))=A_73 | ~v1_relat_1(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_20])).
% 6.17/2.19  tff(c_206, plain, (![A_7]: (k5_relat_1(k4_relat_1(A_7), k6_partfun1(k1_relat_1(A_7)))=k4_relat_1(A_7) | ~v1_relat_1(k4_relat_1(A_7)) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_197])).
% 6.17/2.19  tff(c_1970, plain, (k5_relat_1(k4_relat_1('#skF_3'), k6_partfun1('#skF_1'))=k4_relat_1('#skF_3') | ~v1_relat_1(k4_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1953, c_206])).
% 6.17/2.19  tff(c_1981, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_244, c_226, c_226, c_226, c_1970])).
% 6.17/2.19  tff(c_82, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_217])).
% 6.17/2.19  tff(c_70, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_217])).
% 6.17/2.19  tff(c_80, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_217])).
% 6.17/2.19  tff(c_1919, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_1915])).
% 6.17/2.19  tff(c_1927, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_1919])).
% 6.17/2.19  tff(c_1928, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_70, c_1927])).
% 6.17/2.19  tff(c_1986, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1928])).
% 6.17/2.19  tff(c_46, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.17/2.19  tff(c_255, plain, (![A_75, B_76, D_77]: (r2_relset_1(A_75, B_76, D_77, D_77) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.17/2.19  tff(c_262, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_46, c_255])).
% 6.17/2.19  tff(c_1073, plain, (![A_112, D_116, C_114, F_115, E_113, B_117]: (k1_partfun1(A_112, B_117, C_114, D_116, E_113, F_115)=k5_relat_1(E_113, F_115) | ~m1_subset_1(F_115, k1_zfmisc_1(k2_zfmisc_1(C_114, D_116))) | ~v1_funct_1(F_115) | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(A_112, B_117))) | ~v1_funct_1(E_113))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.17/2.19  tff(c_1077, plain, (![A_112, B_117, E_113]: (k1_partfun1(A_112, B_117, '#skF_2', '#skF_1', E_113, '#skF_4')=k5_relat_1(E_113, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(A_112, B_117))) | ~v1_funct_1(E_113))), inference(resolution, [status(thm)], [c_78, c_1073])).
% 6.17/2.19  tff(c_1104, plain, (![A_121, B_122, E_123]: (k1_partfun1(A_121, B_122, '#skF_2', '#skF_1', E_123, '#skF_4')=k5_relat_1(E_123, '#skF_4') | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~v1_funct_1(E_123))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1077])).
% 6.17/2.19  tff(c_1113, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_1104])).
% 6.17/2.19  tff(c_1120, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1113])).
% 6.17/2.19  tff(c_74, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_217])).
% 6.17/2.19  tff(c_540, plain, (![D_91, C_92, A_93, B_94]: (D_91=C_92 | ~r2_relset_1(A_93, B_94, C_92, D_91) | ~m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.17/2.19  tff(c_548, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_74, c_540])).
% 6.17/2.19  tff(c_563, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_548])).
% 6.17/2.19  tff(c_800, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_563])).
% 6.17/2.19  tff(c_1127, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1120, c_800])).
% 6.17/2.19  tff(c_1423, plain, (![E_140, F_138, B_136, A_137, C_139, D_135]: (m1_subset_1(k1_partfun1(A_137, B_136, C_139, D_135, E_140, F_138), k1_zfmisc_1(k2_zfmisc_1(A_137, D_135))) | ~m1_subset_1(F_138, k1_zfmisc_1(k2_zfmisc_1(C_139, D_135))) | ~v1_funct_1(F_138) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_137, B_136))) | ~v1_funct_1(E_140))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.17/2.19  tff(c_1451, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1120, c_1423])).
% 6.17/2.19  tff(c_1468, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_82, c_78, c_1451])).
% 6.17/2.19  tff(c_1470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1127, c_1468])).
% 6.17/2.19  tff(c_1471, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_563])).
% 6.17/2.19  tff(c_2527, plain, (![A_189, B_190, C_191, D_192]: (k2_relset_1(A_189, B_190, C_191)=B_190 | ~r2_relset_1(B_190, B_190, k1_partfun1(B_190, A_189, A_189, B_190, D_192, C_191), k6_partfun1(B_190)) | ~m1_subset_1(D_192, k1_zfmisc_1(k2_zfmisc_1(B_190, A_189))) | ~v1_funct_2(D_192, B_190, A_189) | ~v1_funct_1(D_192) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))) | ~v1_funct_2(C_191, A_189, B_190) | ~v1_funct_1(C_191))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.17/2.19  tff(c_2533, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1471, c_2527])).
% 6.17/2.19  tff(c_2537, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_88, c_86, c_84, c_262, c_2533])).
% 6.17/2.19  tff(c_2539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1986, c_2537])).
% 6.17/2.19  tff(c_2540, plain, (~v2_funct_1('#skF_4') | k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1928])).
% 6.17/2.19  tff(c_2584, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2540])).
% 6.17/2.19  tff(c_30, plain, (![A_20]: (v2_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.17/2.19  tff(c_89, plain, (![A_20]: (v2_funct_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_30])).
% 6.17/2.19  tff(c_3324, plain, (![C_226, B_222, A_223, D_225, E_224]: (k1_xboole_0=C_226 | v2_funct_1(E_224) | k2_relset_1(A_223, B_222, D_225)!=B_222 | ~v2_funct_1(k1_partfun1(A_223, B_222, B_222, C_226, D_225, E_224)) | ~m1_subset_1(E_224, k1_zfmisc_1(k2_zfmisc_1(B_222, C_226))) | ~v1_funct_2(E_224, B_222, C_226) | ~v1_funct_1(E_224) | ~m1_subset_1(D_225, k1_zfmisc_1(k2_zfmisc_1(A_223, B_222))) | ~v1_funct_2(D_225, A_223, B_222) | ~v1_funct_1(D_225))), inference(cnfTransformation, [status(thm)], [f_175])).
% 6.17/2.19  tff(c_3328, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1471, c_3324])).
% 6.17/2.19  tff(c_3333, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_82, c_80, c_78, c_89, c_76, c_3328])).
% 6.17/2.19  tff(c_3335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2584, c_70, c_3333])).
% 6.17/2.19  tff(c_3337, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2540])).
% 6.17/2.19  tff(c_3336, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2540])).
% 6.17/2.19  tff(c_3442, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3336, c_34])).
% 6.17/2.19  tff(c_3453, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_193, c_82, c_3337, c_94, c_3442])).
% 6.17/2.19  tff(c_18, plain, (![A_16]: (k5_relat_1(k6_relat_1(k1_relat_1(A_16)), A_16)=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.17/2.19  tff(c_92, plain, (![A_16]: (k5_relat_1(k6_partfun1(k1_relat_1(A_16)), A_16)=A_16 | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_18])).
% 6.17/2.19  tff(c_3470, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3453, c_92])).
% 6.17/2.19  tff(c_3480, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_193, c_3470])).
% 6.17/2.19  tff(c_1835, plain, (![A_152, C_154, D_156, F_155, E_153, B_157]: (k1_partfun1(A_152, B_157, C_154, D_156, E_153, F_155)=k5_relat_1(E_153, F_155) | ~m1_subset_1(F_155, k1_zfmisc_1(k2_zfmisc_1(C_154, D_156))) | ~v1_funct_1(F_155) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_152, B_157))) | ~v1_funct_1(E_153))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.17/2.19  tff(c_1839, plain, (![A_152, B_157, E_153]: (k1_partfun1(A_152, B_157, '#skF_2', '#skF_1', E_153, '#skF_4')=k5_relat_1(E_153, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_152, B_157))) | ~v1_funct_1(E_153))), inference(resolution, [status(thm)], [c_78, c_1835])).
% 6.17/2.19  tff(c_4356, plain, (![A_267, B_268, E_269]: (k1_partfun1(A_267, B_268, '#skF_2', '#skF_1', E_269, '#skF_4')=k5_relat_1(E_269, '#skF_4') | ~m1_subset_1(E_269, k1_zfmisc_1(k2_zfmisc_1(A_267, B_268))) | ~v1_funct_1(E_269))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1839])).
% 6.17/2.19  tff(c_4374, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_4356])).
% 6.17/2.19  tff(c_4388, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1471, c_4374])).
% 6.17/2.19  tff(c_3483, plain, (![B_230, C_231, A_232]: (k6_partfun1(B_230)=k5_relat_1(k2_funct_1(C_231), C_231) | k1_xboole_0=B_230 | ~v2_funct_1(C_231) | k2_relset_1(A_232, B_230, C_231)!=B_230 | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_232, B_230))) | ~v1_funct_2(C_231, A_232, B_230) | ~v1_funct_1(C_231))), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.17/2.19  tff(c_3489, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_3483])).
% 6.17/2.19  tff(c_3499, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_76, c_72, c_3489])).
% 6.17/2.19  tff(c_3500, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_3499])).
% 6.17/2.19  tff(c_12, plain, (![A_8, B_12, C_14]: (k5_relat_1(k5_relat_1(A_8, B_12), C_14)=k5_relat_1(A_8, k5_relat_1(B_12, C_14)) | ~v1_relat_1(C_14) | ~v1_relat_1(B_12) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.17/2.19  tff(c_3563, plain, (![C_14]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_14))=k5_relat_1(k6_partfun1('#skF_2'), C_14) | ~v1_relat_1(C_14) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3500, c_12])).
% 6.17/2.19  tff(c_3571, plain, (![C_14]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_14))=k5_relat_1(k6_partfun1('#skF_2'), C_14) | ~v1_relat_1(C_14))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_196, c_3563])).
% 6.17/2.19  tff(c_4392, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4388, c_3571])).
% 6.17/2.19  tff(c_4405, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_193, c_1981, c_3480, c_4392])).
% 6.17/2.19  tff(c_4407, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_4405])).
% 6.17/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.17/2.19  
% 6.17/2.19  Inference rules
% 6.17/2.19  ----------------------
% 6.17/2.19  #Ref     : 0
% 6.17/2.19  #Sup     : 946
% 6.17/2.19  #Fact    : 0
% 6.17/2.19  #Define  : 0
% 6.17/2.19  #Split   : 11
% 6.17/2.19  #Chain   : 0
% 6.17/2.19  #Close   : 0
% 6.17/2.19  
% 6.17/2.19  Ordering : KBO
% 6.17/2.19  
% 6.17/2.19  Simplification rules
% 6.17/2.19  ----------------------
% 6.17/2.19  #Subsume      : 18
% 6.17/2.19  #Demod        : 1362
% 6.17/2.19  #Tautology    : 508
% 6.17/2.19  #SimpNegUnit  : 35
% 6.17/2.19  #BackRed      : 27
% 6.17/2.19  
% 6.17/2.19  #Partial instantiations: 0
% 6.17/2.19  #Strategies tried      : 1
% 6.17/2.19  
% 6.17/2.19  Timing (in seconds)
% 6.17/2.19  ----------------------
% 6.17/2.19  Preprocessing        : 0.38
% 6.17/2.19  Parsing              : 0.21
% 6.17/2.19  CNF conversion       : 0.03
% 6.17/2.19  Main loop            : 1.02
% 6.17/2.19  Inferencing          : 0.34
% 6.17/2.19  Reduction            : 0.40
% 6.17/2.19  Demodulation         : 0.30
% 6.17/2.19  BG Simplification    : 0.04
% 6.17/2.19  Subsumption          : 0.17
% 6.17/2.19  Abstraction          : 0.05
% 6.17/2.19  MUC search           : 0.00
% 6.17/2.19  Cooper               : 0.00
% 6.17/2.19  Total                : 1.44
% 6.17/2.19  Index Insertion      : 0.00
% 6.17/2.19  Index Deletion       : 0.00
% 6.17/2.19  Index Matching       : 0.00
% 6.17/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
