%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:11 EST 2020

% Result     : Theorem 6.48s
% Output     : CNFRefutation 6.77s
% Verified   : 
% Statistics : Number of formulae       :  184 (1244 expanded)
%              Number of leaves         :   43 ( 445 expanded)
%              Depth                    :   10
%              Number of atoms          :  360 (3891 expanded)
%              Number of equality atoms :   94 ( 610 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_153,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_94,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_46,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_88,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_133,axiom,(
    ! [A,B,C,D] :
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_111,axiom,(
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

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_56,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_130,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_48,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_22,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_71,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_22])).

tff(c_40,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28] :
      ( m1_subset_1(k1_partfun1(A_24,B_25,C_26,D_27,E_28,F_29),k1_zfmisc_1(k2_zfmisc_1(A_24,D_27)))
      | ~ m1_subset_1(F_29,k1_zfmisc_1(k2_zfmisc_1(C_26,D_27)))
      | ~ v1_funct_1(F_29)
      | ~ m1_subset_1(E_28,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_1(E_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_46,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_486,plain,(
    ! [D_100,C_101,A_102,B_103] :
      ( D_100 = C_101
      | ~ r2_relset_1(A_102,B_103,C_101,D_100)
      | ~ m1_subset_1(D_100,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103)))
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_492,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_486])).

tff(c_503,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_492])).

tff(c_875,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_503])).

tff(c_968,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_875])).

tff(c_975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_968])).

tff(c_976,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_503])).

tff(c_1026,plain,(
    ! [C_187,E_186,A_183,D_185,B_184] :
      ( k1_xboole_0 = C_187
      | v2_funct_1(D_185)
      | ~ v2_funct_1(k1_partfun1(A_183,B_184,B_184,C_187,D_185,E_186))
      | ~ m1_subset_1(E_186,k1_zfmisc_1(k2_zfmisc_1(B_184,C_187)))
      | ~ v1_funct_2(E_186,B_184,C_187)
      | ~ v1_funct_1(E_186)
      | ~ m1_subset_1(D_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ v1_funct_2(D_185,A_183,B_184)
      | ~ v1_funct_1(D_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1028,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_976,c_1026])).

tff(c_1030,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_71,c_1028])).

tff(c_1031,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_1030])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1062,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1031,c_8])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1060,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1031,c_1031,c_14])).

tff(c_149,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_169,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_149])).

tff(c_197,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_210,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_169,c_197])).

tff(c_368,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_1184,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1060,c_368])).

tff(c_1189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1062,c_1184])).

tff(c_1190,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_1195,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1190,c_66])).

tff(c_1483,plain,(
    ! [D_231,C_232,A_233,B_234] :
      ( D_231 = C_232
      | ~ r2_relset_1(A_233,B_234,C_232,D_231)
      | ~ m1_subset_1(D_231,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1491,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_1483])).

tff(c_1506,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1491])).

tff(c_1570,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1506])).

tff(c_1771,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1570])).

tff(c_1778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1195,c_1190,c_64,c_60,c_1771])).

tff(c_1779,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1506])).

tff(c_2181,plain,(
    ! [E_342,C_343,A_339,D_341,B_340] :
      ( k1_xboole_0 = C_343
      | v2_funct_1(D_341)
      | ~ v2_funct_1(k1_partfun1(A_339,B_340,B_340,C_343,D_341,E_342))
      | ~ m1_subset_1(E_342,k1_zfmisc_1(k2_zfmisc_1(B_340,C_343)))
      | ~ v1_funct_2(E_342,B_340,C_343)
      | ~ v1_funct_1(E_342)
      | ~ m1_subset_1(D_341,k1_zfmisc_1(k2_zfmisc_1(A_339,B_340)))
      | ~ v1_funct_2(D_341,A_339,B_340)
      | ~ v1_funct_1(D_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2183,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1779,c_2181])).

tff(c_2185,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1195,c_1190,c_64,c_62,c_60,c_71,c_2183])).

tff(c_2186,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_2185])).

tff(c_2222,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2186,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2216,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2186,c_2186,c_12])).

tff(c_170,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_149])).

tff(c_209,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_170,c_197])).

tff(c_334,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_2383,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2216,c_334])).

tff(c_2388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2222,c_2383])).

tff(c_2389,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_2393,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2389,c_60])).

tff(c_2707,plain,(
    ! [D_397,C_398,A_399,B_400] :
      ( D_397 = C_398
      | ~ r2_relset_1(A_399,B_400,C_398,D_397)
      | ~ m1_subset_1(D_397,k1_zfmisc_1(k2_zfmisc_1(A_399,B_400)))
      | ~ m1_subset_1(C_398,k1_zfmisc_1(k2_zfmisc_1(A_399,B_400))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2717,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_2707])).

tff(c_2736,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2717])).

tff(c_2800,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2736])).

tff(c_3038,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_2800])).

tff(c_3045,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_2393,c_2389,c_3038])).

tff(c_3046,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2736])).

tff(c_3419,plain,(
    ! [A_507,B_508,C_511,D_509,E_510] :
      ( k1_xboole_0 = C_511
      | v2_funct_1(D_509)
      | ~ v2_funct_1(k1_partfun1(A_507,B_508,B_508,C_511,D_509,E_510))
      | ~ m1_subset_1(E_510,k1_zfmisc_1(k2_zfmisc_1(B_508,C_511)))
      | ~ v1_funct_2(E_510,B_508,C_511)
      | ~ v1_funct_1(E_510)
      | ~ m1_subset_1(D_509,k1_zfmisc_1(k2_zfmisc_1(A_507,B_508)))
      | ~ v1_funct_2(D_509,A_507,B_508)
      | ~ v1_funct_1(D_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3421,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3046,c_3419])).

tff(c_3423,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_2393,c_2389,c_71,c_3421])).

tff(c_3424,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_3423])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2406,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2389,c_10])).

tff(c_2441,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2406])).

tff(c_3447,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3424,c_2441])).

tff(c_3617,plain,(
    ! [A_527] : k2_zfmisc_1(A_527,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3424,c_3424,c_12])).

tff(c_3666,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3617,c_2389])).

tff(c_3696,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3447,c_3666])).

tff(c_3698,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2406])).

tff(c_3724,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3698,c_8])).

tff(c_3718,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3698,c_3698,c_12])).

tff(c_3722,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3698,c_3698,c_14])).

tff(c_3697,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2406])).

tff(c_3883,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3698,c_3698,c_3697])).

tff(c_3884,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3883])).

tff(c_2391,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_3885,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3884,c_2391])).

tff(c_3896,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3724,c_3722,c_3885])).

tff(c_3897,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3883])).

tff(c_3901,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3897,c_2391])).

tff(c_3912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3724,c_3718,c_3901])).

tff(c_3913,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_3934,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3913,c_66])).

tff(c_3916,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2389,c_60])).

tff(c_4458,plain,(
    ! [F_614,A_615,D_616,C_611,B_612,E_613] :
      ( m1_subset_1(k1_partfun1(A_615,B_612,C_611,D_616,E_613,F_614),k1_zfmisc_1(k2_zfmisc_1(A_615,D_616)))
      | ~ m1_subset_1(F_614,k1_zfmisc_1(k2_zfmisc_1(C_611,D_616)))
      | ~ v1_funct_1(F_614)
      | ~ m1_subset_1(E_613,k1_zfmisc_1(k2_zfmisc_1(A_615,B_612)))
      | ~ v1_funct_1(E_613) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4238,plain,(
    ! [D_576,C_577,A_578,B_579] :
      ( D_576 = C_577
      | ~ r2_relset_1(A_578,B_579,C_577,D_576)
      | ~ m1_subset_1(D_576,k1_zfmisc_1(k2_zfmisc_1(A_578,B_579)))
      | ~ m1_subset_1(C_577,k1_zfmisc_1(k2_zfmisc_1(A_578,B_579))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4244,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_4238])).

tff(c_4255,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4244])).

tff(c_4309,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4255])).

tff(c_4461,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4458,c_4309])).

tff(c_4496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3934,c_3913,c_64,c_3916,c_2389,c_4461])).

tff(c_4497,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4255])).

tff(c_4904,plain,(
    ! [B_675,E_677,A_674,C_678,D_676] :
      ( k1_xboole_0 = C_678
      | v2_funct_1(D_676)
      | ~ v2_funct_1(k1_partfun1(A_674,B_675,B_675,C_678,D_676,E_677))
      | ~ m1_subset_1(E_677,k1_zfmisc_1(k2_zfmisc_1(B_675,C_678)))
      | ~ v1_funct_2(E_677,B_675,C_678)
      | ~ v1_funct_1(E_677)
      | ~ m1_subset_1(D_676,k1_zfmisc_1(k2_zfmisc_1(A_674,B_675)))
      | ~ v1_funct_2(D_676,A_674,B_675)
      | ~ v1_funct_1(D_676) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_4906,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4497,c_4904])).

tff(c_4908,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_3934,c_3913,c_64,c_62,c_3916,c_2389,c_71,c_4906])).

tff(c_4909,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_4908])).

tff(c_3947,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_3913,c_10])).

tff(c_3964,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3947])).

tff(c_4934,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4909,c_3964])).

tff(c_4945,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4909,c_4909,c_14])).

tff(c_5106,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4945,c_3913])).

tff(c_5108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4934,c_5106])).

tff(c_5110,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3947])).

tff(c_90,plain,(
    ! [A_49] : k6_relat_1(A_49) = k6_partfun1(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_20,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_96,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_20])).

tff(c_110,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_71])).

tff(c_5146,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5110,c_110])).

tff(c_5154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_5146])).

tff(c_5155,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_5255,plain,(
    ! [C_706,A_707,B_708] :
      ( v1_relat_1(C_706)
      | ~ m1_subset_1(C_706,k1_zfmisc_1(k2_zfmisc_1(A_707,B_708))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_5276,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_5255])).

tff(c_5319,plain,(
    ! [C_715,B_716,A_717] :
      ( v5_relat_1(C_715,B_716)
      | ~ m1_subset_1(C_715,k1_zfmisc_1(k2_zfmisc_1(A_717,B_716))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_5342,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_5319])).

tff(c_5472,plain,(
    ! [A_735,B_736,D_737] :
      ( r2_relset_1(A_735,B_736,D_737,D_737)
      | ~ m1_subset_1(D_737,k1_zfmisc_1(k2_zfmisc_1(A_735,B_736))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5486,plain,(
    ! [A_30] : r2_relset_1(A_30,A_30,k6_partfun1(A_30),k6_partfun1(A_30)) ),
    inference(resolution,[status(thm)],[c_46,c_5472])).

tff(c_5515,plain,(
    ! [A_742,B_743,C_744] :
      ( k2_relset_1(A_742,B_743,C_744) = k2_relat_1(C_744)
      | ~ m1_subset_1(C_744,k1_zfmisc_1(k2_zfmisc_1(A_742,B_743))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5538,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_5515])).

tff(c_5576,plain,(
    ! [D_751,C_752,A_753,B_754] :
      ( D_751 = C_752
      | ~ r2_relset_1(A_753,B_754,C_752,D_751)
      | ~ m1_subset_1(D_751,k1_zfmisc_1(k2_zfmisc_1(A_753,B_754)))
      | ~ m1_subset_1(C_752,k1_zfmisc_1(k2_zfmisc_1(A_753,B_754))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5586,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_5576])).

tff(c_5605,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_5586])).

tff(c_5687,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_5605])).

tff(c_6033,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_5687])).

tff(c_6040,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_6033])).

tff(c_6041,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5605])).

tff(c_6488,plain,(
    ! [A_899,B_900,C_901,D_902] :
      ( k2_relset_1(A_899,B_900,C_901) = B_900
      | ~ r2_relset_1(B_900,B_900,k1_partfun1(B_900,A_899,A_899,B_900,D_902,C_901),k6_partfun1(B_900))
      | ~ m1_subset_1(D_902,k1_zfmisc_1(k2_zfmisc_1(B_900,A_899)))
      | ~ v1_funct_2(D_902,B_900,A_899)
      | ~ v1_funct_1(D_902)
      | ~ m1_subset_1(C_901,k1_zfmisc_1(k2_zfmisc_1(A_899,B_900)))
      | ~ v1_funct_2(C_901,A_899,B_900)
      | ~ v1_funct_1(C_901) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6491,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6041,c_6488])).

tff(c_6496,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_5486,c_5538,c_6491])).

tff(c_36,plain,(
    ! [B_23] :
      ( v2_funct_2(B_23,k2_relat_1(B_23))
      | ~ v5_relat_1(B_23,k2_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6505,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6496,c_36])).

tff(c_6512,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5276,c_5342,c_6496,c_6505])).

tff(c_6514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5155,c_6512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.48/2.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.77/2.40  
% 6.77/2.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.77/2.40  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.77/2.40  
% 6.77/2.40  %Foreground sorts:
% 6.77/2.40  
% 6.77/2.40  
% 6.77/2.40  %Background operators:
% 6.77/2.40  
% 6.77/2.40  
% 6.77/2.40  %Foreground operators:
% 6.77/2.40  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.77/2.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.77/2.40  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.77/2.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.77/2.40  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.77/2.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.77/2.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.77/2.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.77/2.40  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.77/2.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.77/2.40  tff('#skF_2', type, '#skF_2': $i).
% 6.77/2.40  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.77/2.40  tff('#skF_3', type, '#skF_3': $i).
% 6.77/2.40  tff('#skF_1', type, '#skF_1': $i).
% 6.77/2.40  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.77/2.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.77/2.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.77/2.40  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.77/2.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.77/2.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.77/2.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.77/2.40  tff('#skF_4', type, '#skF_4': $i).
% 6.77/2.40  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.77/2.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.77/2.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.77/2.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.77/2.40  
% 6.77/2.44  tff(f_153, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 6.77/2.44  tff(f_94, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.77/2.44  tff(f_46, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 6.77/2.44  tff(f_88, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.77/2.44  tff(f_92, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.77/2.44  tff(f_68, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.77/2.44  tff(f_133, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 6.77/2.44  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.77/2.44  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.77/2.44  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.77/2.44  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.77/2.44  tff(f_44, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 6.77/2.44  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.77/2.44  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.77/2.44  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.77/2.44  tff(f_111, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 6.77/2.44  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.77/2.44  tff(c_56, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.77/2.44  tff(c_130, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 6.77/2.44  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.77/2.44  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.77/2.44  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.77/2.44  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.77/2.44  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.77/2.44  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.77/2.44  tff(c_48, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.77/2.44  tff(c_22, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.77/2.44  tff(c_71, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_22])).
% 6.77/2.44  tff(c_40, plain, (![A_24, B_25, F_29, D_27, C_26, E_28]: (m1_subset_1(k1_partfun1(A_24, B_25, C_26, D_27, E_28, F_29), k1_zfmisc_1(k2_zfmisc_1(A_24, D_27))) | ~m1_subset_1(F_29, k1_zfmisc_1(k2_zfmisc_1(C_26, D_27))) | ~v1_funct_1(F_29) | ~m1_subset_1(E_28, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_1(E_28))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.77/2.44  tff(c_46, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.77/2.44  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.77/2.44  tff(c_486, plain, (![D_100, C_101, A_102, B_103]: (D_100=C_101 | ~r2_relset_1(A_102, B_103, C_101, D_100) | ~m1_subset_1(D_100, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.77/2.44  tff(c_492, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_486])).
% 6.77/2.44  tff(c_503, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_492])).
% 6.77/2.44  tff(c_875, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_503])).
% 6.77/2.44  tff(c_968, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_875])).
% 6.77/2.44  tff(c_975, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_968])).
% 6.77/2.44  tff(c_976, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_503])).
% 6.77/2.44  tff(c_1026, plain, (![C_187, E_186, A_183, D_185, B_184]: (k1_xboole_0=C_187 | v2_funct_1(D_185) | ~v2_funct_1(k1_partfun1(A_183, B_184, B_184, C_187, D_185, E_186)) | ~m1_subset_1(E_186, k1_zfmisc_1(k2_zfmisc_1(B_184, C_187))) | ~v1_funct_2(E_186, B_184, C_187) | ~v1_funct_1(E_186) | ~m1_subset_1(D_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~v1_funct_2(D_185, A_183, B_184) | ~v1_funct_1(D_185))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.77/2.44  tff(c_1028, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_976, c_1026])).
% 6.77/2.44  tff(c_1030, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_71, c_1028])).
% 6.77/2.44  tff(c_1031, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_130, c_1030])).
% 6.77/2.44  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.77/2.44  tff(c_1062, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1031, c_8])).
% 6.77/2.44  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.77/2.44  tff(c_1060, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1031, c_1031, c_14])).
% 6.77/2.44  tff(c_149, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.77/2.44  tff(c_169, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_149])).
% 6.77/2.44  tff(c_197, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.77/2.44  tff(c_210, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_169, c_197])).
% 6.77/2.44  tff(c_368, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_210])).
% 6.77/2.44  tff(c_1184, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1060, c_368])).
% 6.77/2.44  tff(c_1189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1062, c_1184])).
% 6.77/2.44  tff(c_1190, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_210])).
% 6.77/2.44  tff(c_1195, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1190, c_66])).
% 6.77/2.44  tff(c_1483, plain, (![D_231, C_232, A_233, B_234]: (D_231=C_232 | ~r2_relset_1(A_233, B_234, C_232, D_231) | ~m1_subset_1(D_231, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.77/2.44  tff(c_1491, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_1483])).
% 6.77/2.44  tff(c_1506, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1491])).
% 6.77/2.44  tff(c_1570, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1506])).
% 6.77/2.44  tff(c_1771, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_1570])).
% 6.77/2.44  tff(c_1778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1195, c_1190, c_64, c_60, c_1771])).
% 6.77/2.44  tff(c_1779, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1506])).
% 6.77/2.44  tff(c_2181, plain, (![E_342, C_343, A_339, D_341, B_340]: (k1_xboole_0=C_343 | v2_funct_1(D_341) | ~v2_funct_1(k1_partfun1(A_339, B_340, B_340, C_343, D_341, E_342)) | ~m1_subset_1(E_342, k1_zfmisc_1(k2_zfmisc_1(B_340, C_343))) | ~v1_funct_2(E_342, B_340, C_343) | ~v1_funct_1(E_342) | ~m1_subset_1(D_341, k1_zfmisc_1(k2_zfmisc_1(A_339, B_340))) | ~v1_funct_2(D_341, A_339, B_340) | ~v1_funct_1(D_341))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.77/2.44  tff(c_2183, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1779, c_2181])).
% 6.77/2.44  tff(c_2185, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1195, c_1190, c_64, c_62, c_60, c_71, c_2183])).
% 6.77/2.44  tff(c_2186, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_130, c_2185])).
% 6.77/2.44  tff(c_2222, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2186, c_8])).
% 6.77/2.44  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.77/2.44  tff(c_2216, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2186, c_2186, c_12])).
% 6.77/2.44  tff(c_170, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_149])).
% 6.77/2.44  tff(c_209, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), '#skF_4')), inference(resolution, [status(thm)], [c_170, c_197])).
% 6.77/2.44  tff(c_334, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), '#skF_4')), inference(splitLeft, [status(thm)], [c_209])).
% 6.77/2.44  tff(c_2383, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2216, c_334])).
% 6.77/2.44  tff(c_2388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2222, c_2383])).
% 6.77/2.44  tff(c_2389, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_209])).
% 6.77/2.44  tff(c_2393, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2389, c_60])).
% 6.77/2.44  tff(c_2707, plain, (![D_397, C_398, A_399, B_400]: (D_397=C_398 | ~r2_relset_1(A_399, B_400, C_398, D_397) | ~m1_subset_1(D_397, k1_zfmisc_1(k2_zfmisc_1(A_399, B_400))) | ~m1_subset_1(C_398, k1_zfmisc_1(k2_zfmisc_1(A_399, B_400))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.77/2.44  tff(c_2717, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_2707])).
% 6.77/2.44  tff(c_2736, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2717])).
% 6.77/2.44  tff(c_2800, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2736])).
% 6.77/2.44  tff(c_3038, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_2800])).
% 6.77/2.44  tff(c_3045, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_2393, c_2389, c_3038])).
% 6.77/2.44  tff(c_3046, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2736])).
% 6.77/2.44  tff(c_3419, plain, (![A_507, B_508, C_511, D_509, E_510]: (k1_xboole_0=C_511 | v2_funct_1(D_509) | ~v2_funct_1(k1_partfun1(A_507, B_508, B_508, C_511, D_509, E_510)) | ~m1_subset_1(E_510, k1_zfmisc_1(k2_zfmisc_1(B_508, C_511))) | ~v1_funct_2(E_510, B_508, C_511) | ~v1_funct_1(E_510) | ~m1_subset_1(D_509, k1_zfmisc_1(k2_zfmisc_1(A_507, B_508))) | ~v1_funct_2(D_509, A_507, B_508) | ~v1_funct_1(D_509))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.77/2.44  tff(c_3421, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3046, c_3419])).
% 6.77/2.44  tff(c_3423, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_2393, c_2389, c_71, c_3421])).
% 6.77/2.44  tff(c_3424, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_130, c_3423])).
% 6.77/2.44  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.77/2.44  tff(c_2406, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2389, c_10])).
% 6.77/2.44  tff(c_2441, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_2406])).
% 6.77/2.44  tff(c_3447, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3424, c_2441])).
% 6.77/2.44  tff(c_3617, plain, (![A_527]: (k2_zfmisc_1(A_527, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3424, c_3424, c_12])).
% 6.77/2.44  tff(c_3666, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3617, c_2389])).
% 6.77/2.44  tff(c_3696, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3447, c_3666])).
% 6.77/2.44  tff(c_3698, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2406])).
% 6.77/2.44  tff(c_3724, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3698, c_8])).
% 6.77/2.44  tff(c_3718, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3698, c_3698, c_12])).
% 6.77/2.44  tff(c_3722, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3698, c_3698, c_14])).
% 6.77/2.44  tff(c_3697, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_2406])).
% 6.77/2.44  tff(c_3883, plain, ('#skF_2'='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3698, c_3698, c_3697])).
% 6.77/2.44  tff(c_3884, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_3883])).
% 6.77/2.44  tff(c_2391, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_210])).
% 6.77/2.44  tff(c_3885, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3884, c_2391])).
% 6.77/2.44  tff(c_3896, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3724, c_3722, c_3885])).
% 6.77/2.44  tff(c_3897, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_3883])).
% 6.77/2.44  tff(c_3901, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3897, c_2391])).
% 6.77/2.44  tff(c_3912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3724, c_3718, c_3901])).
% 6.77/2.44  tff(c_3913, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_210])).
% 6.77/2.44  tff(c_3934, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3913, c_66])).
% 6.77/2.44  tff(c_3916, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2389, c_60])).
% 6.77/2.44  tff(c_4458, plain, (![F_614, A_615, D_616, C_611, B_612, E_613]: (m1_subset_1(k1_partfun1(A_615, B_612, C_611, D_616, E_613, F_614), k1_zfmisc_1(k2_zfmisc_1(A_615, D_616))) | ~m1_subset_1(F_614, k1_zfmisc_1(k2_zfmisc_1(C_611, D_616))) | ~v1_funct_1(F_614) | ~m1_subset_1(E_613, k1_zfmisc_1(k2_zfmisc_1(A_615, B_612))) | ~v1_funct_1(E_613))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.77/2.44  tff(c_4238, plain, (![D_576, C_577, A_578, B_579]: (D_576=C_577 | ~r2_relset_1(A_578, B_579, C_577, D_576) | ~m1_subset_1(D_576, k1_zfmisc_1(k2_zfmisc_1(A_578, B_579))) | ~m1_subset_1(C_577, k1_zfmisc_1(k2_zfmisc_1(A_578, B_579))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.77/2.44  tff(c_4244, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_4238])).
% 6.77/2.44  tff(c_4255, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4244])).
% 6.77/2.44  tff(c_4309, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_4255])).
% 6.77/2.44  tff(c_4461, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4458, c_4309])).
% 6.77/2.44  tff(c_4496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_3934, c_3913, c_64, c_3916, c_2389, c_4461])).
% 6.77/2.44  tff(c_4497, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_4255])).
% 6.77/2.44  tff(c_4904, plain, (![B_675, E_677, A_674, C_678, D_676]: (k1_xboole_0=C_678 | v2_funct_1(D_676) | ~v2_funct_1(k1_partfun1(A_674, B_675, B_675, C_678, D_676, E_677)) | ~m1_subset_1(E_677, k1_zfmisc_1(k2_zfmisc_1(B_675, C_678))) | ~v1_funct_2(E_677, B_675, C_678) | ~v1_funct_1(E_677) | ~m1_subset_1(D_676, k1_zfmisc_1(k2_zfmisc_1(A_674, B_675))) | ~v1_funct_2(D_676, A_674, B_675) | ~v1_funct_1(D_676))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.77/2.44  tff(c_4906, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4497, c_4904])).
% 6.77/2.44  tff(c_4908, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_3934, c_3913, c_64, c_62, c_3916, c_2389, c_71, c_4906])).
% 6.77/2.44  tff(c_4909, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_130, c_4908])).
% 6.77/2.44  tff(c_3947, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_3913, c_10])).
% 6.77/2.44  tff(c_3964, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_3947])).
% 6.77/2.44  tff(c_4934, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4909, c_3964])).
% 6.77/2.44  tff(c_4945, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4909, c_4909, c_14])).
% 6.77/2.44  tff(c_5106, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4945, c_3913])).
% 6.77/2.44  tff(c_5108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4934, c_5106])).
% 6.77/2.44  tff(c_5110, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3947])).
% 6.77/2.44  tff(c_90, plain, (![A_49]: (k6_relat_1(A_49)=k6_partfun1(A_49))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.77/2.44  tff(c_20, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.77/2.44  tff(c_96, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_90, c_20])).
% 6.77/2.44  tff(c_110, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_96, c_71])).
% 6.77/2.44  tff(c_5146, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5110, c_110])).
% 6.77/2.44  tff(c_5154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_5146])).
% 6.77/2.44  tff(c_5155, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 6.77/2.44  tff(c_5255, plain, (![C_706, A_707, B_708]: (v1_relat_1(C_706) | ~m1_subset_1(C_706, k1_zfmisc_1(k2_zfmisc_1(A_707, B_708))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.77/2.44  tff(c_5276, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_5255])).
% 6.77/2.44  tff(c_5319, plain, (![C_715, B_716, A_717]: (v5_relat_1(C_715, B_716) | ~m1_subset_1(C_715, k1_zfmisc_1(k2_zfmisc_1(A_717, B_716))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.77/2.44  tff(c_5342, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_5319])).
% 6.77/2.44  tff(c_5472, plain, (![A_735, B_736, D_737]: (r2_relset_1(A_735, B_736, D_737, D_737) | ~m1_subset_1(D_737, k1_zfmisc_1(k2_zfmisc_1(A_735, B_736))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.77/2.44  tff(c_5486, plain, (![A_30]: (r2_relset_1(A_30, A_30, k6_partfun1(A_30), k6_partfun1(A_30)))), inference(resolution, [status(thm)], [c_46, c_5472])).
% 6.77/2.44  tff(c_5515, plain, (![A_742, B_743, C_744]: (k2_relset_1(A_742, B_743, C_744)=k2_relat_1(C_744) | ~m1_subset_1(C_744, k1_zfmisc_1(k2_zfmisc_1(A_742, B_743))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.77/2.44  tff(c_5538, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_5515])).
% 6.77/2.44  tff(c_5576, plain, (![D_751, C_752, A_753, B_754]: (D_751=C_752 | ~r2_relset_1(A_753, B_754, C_752, D_751) | ~m1_subset_1(D_751, k1_zfmisc_1(k2_zfmisc_1(A_753, B_754))) | ~m1_subset_1(C_752, k1_zfmisc_1(k2_zfmisc_1(A_753, B_754))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.77/2.44  tff(c_5586, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_5576])).
% 6.77/2.44  tff(c_5605, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_5586])).
% 6.77/2.44  tff(c_5687, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_5605])).
% 6.77/2.44  tff(c_6033, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_5687])).
% 6.77/2.44  tff(c_6040, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_6033])).
% 6.77/2.44  tff(c_6041, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_5605])).
% 6.77/2.44  tff(c_6488, plain, (![A_899, B_900, C_901, D_902]: (k2_relset_1(A_899, B_900, C_901)=B_900 | ~r2_relset_1(B_900, B_900, k1_partfun1(B_900, A_899, A_899, B_900, D_902, C_901), k6_partfun1(B_900)) | ~m1_subset_1(D_902, k1_zfmisc_1(k2_zfmisc_1(B_900, A_899))) | ~v1_funct_2(D_902, B_900, A_899) | ~v1_funct_1(D_902) | ~m1_subset_1(C_901, k1_zfmisc_1(k2_zfmisc_1(A_899, B_900))) | ~v1_funct_2(C_901, A_899, B_900) | ~v1_funct_1(C_901))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.77/2.44  tff(c_6491, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6041, c_6488])).
% 6.77/2.44  tff(c_6496, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_5486, c_5538, c_6491])).
% 6.77/2.44  tff(c_36, plain, (![B_23]: (v2_funct_2(B_23, k2_relat_1(B_23)) | ~v5_relat_1(B_23, k2_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.77/2.44  tff(c_6505, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6496, c_36])).
% 6.77/2.44  tff(c_6512, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5276, c_5342, c_6496, c_6505])).
% 6.77/2.44  tff(c_6514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5155, c_6512])).
% 6.77/2.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.77/2.44  
% 6.77/2.44  Inference rules
% 6.77/2.44  ----------------------
% 6.77/2.44  #Ref     : 0
% 6.77/2.44  #Sup     : 1426
% 6.77/2.44  #Fact    : 0
% 6.77/2.44  #Define  : 0
% 6.77/2.44  #Split   : 29
% 6.77/2.44  #Chain   : 0
% 6.77/2.44  #Close   : 0
% 6.77/2.44  
% 6.77/2.44  Ordering : KBO
% 6.77/2.44  
% 6.77/2.44  Simplification rules
% 6.77/2.44  ----------------------
% 6.77/2.44  #Subsume      : 127
% 6.77/2.44  #Demod        : 1229
% 6.77/2.44  #Tautology    : 679
% 6.77/2.44  #SimpNegUnit  : 9
% 6.77/2.44  #BackRed      : 218
% 6.77/2.44  
% 6.77/2.44  #Partial instantiations: 0
% 6.77/2.44  #Strategies tried      : 1
% 6.77/2.44  
% 6.77/2.44  Timing (in seconds)
% 6.77/2.44  ----------------------
% 6.77/2.44  Preprocessing        : 0.35
% 6.77/2.44  Parsing              : 0.19
% 6.77/2.44  CNF conversion       : 0.02
% 6.77/2.44  Main loop            : 1.29
% 6.77/2.44  Inferencing          : 0.46
% 6.77/2.44  Reduction            : 0.46
% 6.77/2.44  Demodulation         : 0.33
% 6.77/2.44  BG Simplification    : 0.04
% 6.77/2.44  Subsumption          : 0.21
% 6.77/2.44  Abstraction          : 0.05
% 6.77/2.44  MUC search           : 0.00
% 6.77/2.44  Cooper               : 0.00
% 6.77/2.44  Total                : 1.71
% 6.77/2.44  Index Insertion      : 0.00
% 6.77/2.44  Index Deletion       : 0.00
% 6.77/2.44  Index Matching       : 0.00
% 6.77/2.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
