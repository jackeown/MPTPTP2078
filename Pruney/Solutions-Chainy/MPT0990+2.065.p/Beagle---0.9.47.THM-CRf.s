%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:05 EST 2020

% Result     : Theorem 8.00s
% Output     : CNFRefutation 8.06s
% Verified   : 
% Statistics : Number of formulae       :  176 (1070 expanded)
%              Number of leaves         :   50 ( 397 expanded)
%              Depth                    :   18
%              Number of atoms          :  393 (4167 expanded)
%              Number of equality atoms :  126 (1469 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_230,negated_conjecture,(
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

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_145,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_204,axiom,(
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

tff(f_121,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_119,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_143,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_133,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_162,axiom,(
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

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_73,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_188,axiom,(
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

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_74,plain,(
    k2_funct_1('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_92,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_193,plain,(
    ! [C_78,A_79,B_80] :
      ( v1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_213,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_193])).

tff(c_96,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_26,plain,(
    ! [A_17] :
      ( v1_relat_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_80,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_84,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_334,plain,(
    ! [A_98,B_99,C_100] :
      ( k2_relset_1(A_98,B_99,C_100) = k2_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_344,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_334])).

tff(c_356,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_344])).

tff(c_230,plain,(
    ! [A_85] :
      ( k1_relat_1(k2_funct_1(A_85)) = k2_relat_1(A_85)
      | ~ v2_funct_1(A_85)
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_58,plain,(
    ! [A_45] : k6_relat_1(A_45) = k6_partfun1(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_20,plain,(
    ! [A_14] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_14)),A_14) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_102,plain,(
    ! [A_14] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_14)),A_14) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_20])).

tff(c_7695,plain,(
    ! [A_419] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_419)),k2_funct_1(A_419)) = k2_funct_1(A_419)
      | ~ v1_relat_1(k2_funct_1(A_419))
      | ~ v2_funct_1(A_419)
      | ~ v1_funct_1(A_419)
      | ~ v1_relat_1(A_419) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_102])).

tff(c_7719,plain,
    ( k5_relat_1(k6_partfun1('#skF_3'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_7695])).

tff(c_7736,plain,
    ( k5_relat_1(k6_partfun1('#skF_3'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_96,c_80,c_7719])).

tff(c_7739,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7736])).

tff(c_7742,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_7739])).

tff(c_7746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_96,c_7742])).

tff(c_7748,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7736])).

tff(c_86,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_214,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_193])).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [A_64] :
      ( k1_xboole_0 = A_64
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_121,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_117])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_124,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_78])).

tff(c_90,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_88,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_357,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_334])).

tff(c_70,plain,(
    ! [B_58,C_59,A_57] :
      ( k6_partfun1(B_58) = k5_relat_1(k2_funct_1(C_59),C_59)
      | k1_xboole_0 = B_58
      | ~ v2_funct_1(C_59)
      | k2_relset_1(A_57,B_58,C_59) != B_58
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_2(C_59,A_57,B_58)
      | ~ v1_funct_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_5523,plain,(
    ! [B_325,C_326,A_327] :
      ( k6_partfun1(B_325) = k5_relat_1(k2_funct_1(C_326),C_326)
      | B_325 = '#skF_1'
      | ~ v2_funct_1(C_326)
      | k2_relset_1(A_327,B_325,C_326) != B_325
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(A_327,B_325)))
      | ~ v1_funct_2(C_326,A_327,B_325)
      | ~ v1_funct_1(C_326) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_70])).

tff(c_5532,plain,
    ( k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_2','#skF_5') != '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_5523])).

tff(c_5546,plain,
    ( k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5')
    | k2_relat_1('#skF_5') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_357,c_5532])).

tff(c_5547,plain,
    ( k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_5')
    | k2_relat_1('#skF_5') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_5546])).

tff(c_5574,plain,(
    k2_relat_1('#skF_5') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5547])).

tff(c_94,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_50,plain,(
    ! [A_32] : m1_subset_1(k6_relat_1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_97,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50])).

tff(c_315,plain,(
    ! [A_94,B_95,D_96] :
      ( r2_relset_1(A_94,B_95,D_96,D_96)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_329,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_97,c_315])).

tff(c_5282,plain,(
    ! [C_315,D_316,E_318,B_314,F_317,A_313] :
      ( k1_partfun1(A_313,B_314,C_315,D_316,E_318,F_317) = k5_relat_1(E_318,F_317)
      | ~ m1_subset_1(F_317,k1_zfmisc_1(k2_zfmisc_1(C_315,D_316)))
      | ~ v1_funct_1(F_317)
      | ~ m1_subset_1(E_318,k1_zfmisc_1(k2_zfmisc_1(A_313,B_314)))
      | ~ v1_funct_1(E_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_5291,plain,(
    ! [A_313,B_314,E_318] :
      ( k1_partfun1(A_313,B_314,'#skF_3','#skF_2',E_318,'#skF_5') = k5_relat_1(E_318,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_318,k1_zfmisc_1(k2_zfmisc_1(A_313,B_314)))
      | ~ v1_funct_1(E_318) ) ),
    inference(resolution,[status(thm)],[c_86,c_5282])).

tff(c_5575,plain,(
    ! [A_328,B_329,E_330] :
      ( k1_partfun1(A_328,B_329,'#skF_3','#skF_2',E_330,'#skF_5') = k5_relat_1(E_330,'#skF_5')
      | ~ m1_subset_1(E_330,k1_zfmisc_1(k2_zfmisc_1(A_328,B_329)))
      | ~ v1_funct_1(E_330) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_5291])).

tff(c_5585,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_5575])).

tff(c_5597,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_5585])).

tff(c_5750,plain,(
    ! [A_337,F_340,C_339,D_341,B_342,E_338] :
      ( m1_subset_1(k1_partfun1(A_337,B_342,C_339,D_341,E_338,F_340),k1_zfmisc_1(k2_zfmisc_1(A_337,D_341)))
      | ~ m1_subset_1(F_340,k1_zfmisc_1(k2_zfmisc_1(C_339,D_341)))
      | ~ v1_funct_1(F_340)
      | ~ m1_subset_1(E_338,k1_zfmisc_1(k2_zfmisc_1(A_337,B_342)))
      | ~ v1_funct_1(E_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_5790,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5597,c_5750])).

tff(c_5808,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_90,c_86,c_5790])).

tff(c_82,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_655,plain,(
    ! [D_122,C_123,A_124,B_125] :
      ( D_122 = C_123
      | ~ r2_relset_1(A_124,B_125,C_123,D_122)
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_665,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_82,c_655])).

tff(c_684,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_665])).

tff(c_6041,plain,(
    k5_relat_1('#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5808,c_5597,c_5597,c_684])).

tff(c_6047,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6041,c_5597])).

tff(c_6173,plain,(
    ! [A_351,B_352,C_353,D_354] :
      ( k2_relset_1(A_351,B_352,C_353) = B_352
      | ~ r2_relset_1(B_352,B_352,k1_partfun1(B_352,A_351,A_351,B_352,D_354,C_353),k6_partfun1(B_352))
      | ~ m1_subset_1(D_354,k1_zfmisc_1(k2_zfmisc_1(B_352,A_351)))
      | ~ v1_funct_2(D_354,B_352,A_351)
      | ~ v1_funct_1(D_354)
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_zfmisc_1(A_351,B_352)))
      | ~ v1_funct_2(C_353,A_351,B_352)
      | ~ v1_funct_1(C_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_6176,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6047,c_6173])).

tff(c_6181,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_96,c_94,c_92,c_329,c_357,c_6176])).

tff(c_6183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5574,c_6181])).

tff(c_6185,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5547])).

tff(c_6,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k2_subset_1(A_3),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_105,plain,(
    ! [A_3] : m1_subset_1(A_3,k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_170,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(A_74,B_75)
      | ~ m1_subset_1(A_74,k1_zfmisc_1(B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_190,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_105,c_170])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( k5_relat_1(B_16,k6_relat_1(A_15)) = B_16
      | ~ r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_284,plain,(
    ! [B_91,A_92] :
      ( k5_relat_1(B_91,k6_partfun1(A_92)) = B_91
      | ~ r1_tarski(k2_relat_1(B_91),A_92)
      | ~ v1_relat_1(B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_22])).

tff(c_295,plain,(
    ! [B_91] :
      ( k5_relat_1(B_91,k6_partfun1(k2_relat_1(B_91))) = B_91
      | ~ v1_relat_1(B_91) ) ),
    inference(resolution,[status(thm)],[c_190,c_284])).

tff(c_6190,plain,
    ( k5_relat_1('#skF_5',k6_partfun1('#skF_2')) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6185,c_295])).

tff(c_6197,plain,(
    k5_relat_1('#skF_5',k6_partfun1('#skF_2')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_6190])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_123,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_76])).

tff(c_72,plain,(
    ! [A_57,C_59,B_58] :
      ( k6_partfun1(A_57) = k5_relat_1(C_59,k2_funct_1(C_59))
      | k1_xboole_0 = B_58
      | ~ v2_funct_1(C_59)
      | k2_relset_1(A_57,B_58,C_59) != B_58
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_2(C_59,A_57,B_58)
      | ~ v1_funct_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_6992,plain,(
    ! [A_385,C_386,B_387] :
      ( k6_partfun1(A_385) = k5_relat_1(C_386,k2_funct_1(C_386))
      | B_387 = '#skF_1'
      | ~ v2_funct_1(C_386)
      | k2_relset_1(A_385,B_387,C_386) != B_387
      | ~ m1_subset_1(C_386,k1_zfmisc_1(k2_zfmisc_1(A_385,B_387)))
      | ~ v1_funct_2(C_386,A_385,B_387)
      | ~ v1_funct_1(C_386) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_72])).

tff(c_6999,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_6992])).

tff(c_7011,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_84,c_80,c_6999])).

tff(c_7012,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_7011])).

tff(c_6184,plain,
    ( ~ v2_funct_1('#skF_5')
    | k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_5547])).

tff(c_6277,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6184])).

tff(c_28,plain,(
    ! [A_18] : v2_funct_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_100,plain,(
    ! [A_18] : v2_funct_1(k6_partfun1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_28])).

tff(c_6219,plain,(
    ! [A_355,B_356,E_357] :
      ( k1_partfun1(A_355,B_356,'#skF_3','#skF_2',E_357,'#skF_5') = k5_relat_1(E_357,'#skF_5')
      | ~ m1_subset_1(E_357,k1_zfmisc_1(k2_zfmisc_1(A_355,B_356)))
      | ~ v1_funct_1(E_357) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_5291])).

tff(c_6229,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_6219])).

tff(c_6241,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_6229])).

tff(c_6434,plain,(
    ! [C_364,F_365,D_366,B_367,A_362,E_363] :
      ( m1_subset_1(k1_partfun1(A_362,B_367,C_364,D_366,E_363,F_365),k1_zfmisc_1(k2_zfmisc_1(A_362,D_366)))
      | ~ m1_subset_1(F_365,k1_zfmisc_1(k2_zfmisc_1(C_364,D_366)))
      | ~ v1_funct_1(F_365)
      | ~ m1_subset_1(E_363,k1_zfmisc_1(k2_zfmisc_1(A_362,B_367)))
      | ~ v1_funct_1(E_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_6465,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6241,c_6434])).

tff(c_6478,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_90,c_86,c_6465])).

tff(c_6785,plain,(
    k5_relat_1('#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6478,c_6241,c_6241,c_684])).

tff(c_6792,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6785,c_6241])).

tff(c_64,plain,(
    ! [B_52,C_53,D_54,A_51,E_56] :
      ( k1_xboole_0 = C_53
      | v2_funct_1(E_56)
      | k2_relset_1(A_51,B_52,D_54) != B_52
      | ~ v2_funct_1(k1_partfun1(A_51,B_52,B_52,C_53,D_54,E_56))
      | ~ m1_subset_1(E_56,k1_zfmisc_1(k2_zfmisc_1(B_52,C_53)))
      | ~ v1_funct_2(E_56,B_52,C_53)
      | ~ v1_funct_1(E_56)
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ v1_funct_2(D_54,A_51,B_52)
      | ~ v1_funct_1(D_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_6885,plain,(
    ! [B_52,C_53,D_54,A_51,E_56] :
      ( C_53 = '#skF_1'
      | v2_funct_1(E_56)
      | k2_relset_1(A_51,B_52,D_54) != B_52
      | ~ v2_funct_1(k1_partfun1(A_51,B_52,B_52,C_53,D_54,E_56))
      | ~ m1_subset_1(E_56,k1_zfmisc_1(k2_zfmisc_1(B_52,C_53)))
      | ~ v1_funct_2(E_56,B_52,C_53)
      | ~ v1_funct_1(E_56)
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ v1_funct_2(D_54,A_51,B_52)
      | ~ v1_funct_1(D_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_64])).

tff(c_6894,plain,
    ( '#skF_2' = '#skF_1'
    | v2_funct_1('#skF_5')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6792,c_6885])).

tff(c_6901,plain,
    ( '#skF_2' = '#skF_1'
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_92,c_90,c_88,c_86,c_100,c_84,c_6894])).

tff(c_6903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6277,c_124,c_6901])).

tff(c_6905,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_6184])).

tff(c_7713,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_5')) = k2_funct_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6185,c_7695])).

tff(c_7734,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_5')) = k2_funct_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_90,c_6905,c_7713])).

tff(c_7774,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_7734])).

tff(c_7777,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_7774])).

tff(c_7781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_90,c_7777])).

tff(c_7783,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_7734])).

tff(c_362,plain,
    ( k5_relat_1('#skF_4',k6_partfun1('#skF_3')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_295])).

tff(c_369,plain,(
    k5_relat_1('#skF_4',k6_partfun1('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_362])).

tff(c_6186,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6185,c_357])).

tff(c_7001,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_2','#skF_5') != '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_6992])).

tff(c_7015,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_6186,c_6905,c_7001])).

tff(c_7016,plain,(
    k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_7015])).

tff(c_7122,plain,(
    ! [F_391,D_392,B_393,E_389,C_390,A_388] :
      ( m1_subset_1(k1_partfun1(A_388,B_393,C_390,D_392,E_389,F_391),k1_zfmisc_1(k2_zfmisc_1(A_388,D_392)))
      | ~ m1_subset_1(F_391,k1_zfmisc_1(k2_zfmisc_1(C_390,D_392)))
      | ~ v1_funct_1(F_391)
      | ~ m1_subset_1(E_389,k1_zfmisc_1(k2_zfmisc_1(A_388,B_393)))
      | ~ v1_funct_1(E_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_7156,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6241,c_7122])).

tff(c_7171,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_90,c_86,c_7156])).

tff(c_7606,plain,(
    k5_relat_1('#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7171,c_6241,c_6241,c_684])).

tff(c_14,plain,(
    ! [A_6,B_10,C_12] :
      ( k5_relat_1(k5_relat_1(A_6,B_10),C_12) = k5_relat_1(A_6,k5_relat_1(B_10,C_12))
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_7625,plain,(
    ! [C_12] :
      ( k5_relat_1(k6_partfun1('#skF_2'),C_12) = k5_relat_1('#skF_4',k5_relat_1('#skF_5',C_12))
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7606,c_14])).

tff(c_7937,plain,(
    ! [C_423] :
      ( k5_relat_1(k6_partfun1('#skF_2'),C_423) = k5_relat_1('#skF_4',k5_relat_1('#skF_5',C_423))
      | ~ v1_relat_1(C_423) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_214,c_7625])).

tff(c_7782,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_5')) = k2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_7734])).

tff(c_7946,plain,
    ( k5_relat_1('#skF_4',k5_relat_1('#skF_5',k2_funct_1('#skF_5'))) = k2_funct_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7937,c_7782])).

tff(c_8018,plain,(
    k2_funct_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7783,c_369,c_7016,c_7946])).

tff(c_8052,plain,(
    k5_relat_1('#skF_5','#skF_4') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8018,c_7016])).

tff(c_8174,plain,(
    ! [C_12] :
      ( k5_relat_1(k6_partfun1('#skF_3'),C_12) = k5_relat_1('#skF_5',k5_relat_1('#skF_4',C_12))
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8052,c_14])).

tff(c_8506,plain,(
    ! [C_439] :
      ( k5_relat_1(k6_partfun1('#skF_3'),C_439) = k5_relat_1('#skF_5',k5_relat_1('#skF_4',C_439))
      | ~ v1_relat_1(C_439) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_213,c_8174])).

tff(c_7747,plain,(
    k5_relat_1(k6_partfun1('#skF_3'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_7736])).

tff(c_8519,plain,
    ( k5_relat_1('#skF_5',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8506,c_7747])).

tff(c_8599,plain,(
    k2_funct_1('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7748,c_6197,c_7012,c_8519])).

tff(c_8601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_8599])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.00/2.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.00/2.82  
% 8.00/2.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.06/2.82  %$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.06/2.82  
% 8.06/2.82  %Foreground sorts:
% 8.06/2.82  
% 8.06/2.82  
% 8.06/2.82  %Background operators:
% 8.06/2.82  
% 8.06/2.82  
% 8.06/2.82  %Foreground operators:
% 8.06/2.82  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.06/2.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.06/2.82  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.06/2.82  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.06/2.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.06/2.82  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.06/2.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.06/2.82  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.06/2.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.06/2.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.06/2.82  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.06/2.82  tff('#skF_5', type, '#skF_5': $i).
% 8.06/2.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.06/2.82  tff('#skF_2', type, '#skF_2': $i).
% 8.06/2.82  tff('#skF_3', type, '#skF_3': $i).
% 8.06/2.82  tff('#skF_1', type, '#skF_1': $i).
% 8.06/2.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.06/2.82  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.06/2.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.06/2.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.06/2.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.06/2.82  tff('#skF_4', type, '#skF_4': $i).
% 8.06/2.82  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.06/2.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.06/2.82  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.06/2.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.06/2.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.06/2.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.06/2.82  
% 8.06/2.85  tff(f_230, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 8.06/2.85  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.06/2.85  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.06/2.85  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.06/2.85  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 8.06/2.85  tff(f_145, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.06/2.85  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 8.06/2.85  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 8.06/2.85  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.06/2.85  tff(f_204, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 8.06/2.85  tff(f_121, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 8.06/2.85  tff(f_119, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.06/2.85  tff(f_143, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.06/2.85  tff(f_133, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.06/2.85  tff(f_162, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 8.06/2.85  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 8.06/2.85  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 8.06/2.85  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.06/2.85  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 8.06/2.85  tff(f_73, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 8.06/2.85  tff(f_188, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 8.06/2.85  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 8.06/2.85  tff(c_74, plain, (k2_funct_1('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.06/2.85  tff(c_92, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.06/2.85  tff(c_193, plain, (![C_78, A_79, B_80]: (v1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.06/2.85  tff(c_213, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_193])).
% 8.06/2.85  tff(c_96, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.06/2.85  tff(c_26, plain, (![A_17]: (v1_relat_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.06/2.85  tff(c_80, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.06/2.85  tff(c_84, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.06/2.85  tff(c_334, plain, (![A_98, B_99, C_100]: (k2_relset_1(A_98, B_99, C_100)=k2_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.06/2.85  tff(c_344, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_334])).
% 8.06/2.85  tff(c_356, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_344])).
% 8.06/2.85  tff(c_230, plain, (![A_85]: (k1_relat_1(k2_funct_1(A_85))=k2_relat_1(A_85) | ~v2_funct_1(A_85) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.06/2.85  tff(c_58, plain, (![A_45]: (k6_relat_1(A_45)=k6_partfun1(A_45))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.06/2.85  tff(c_20, plain, (![A_14]: (k5_relat_1(k6_relat_1(k1_relat_1(A_14)), A_14)=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.06/2.85  tff(c_102, plain, (![A_14]: (k5_relat_1(k6_partfun1(k1_relat_1(A_14)), A_14)=A_14 | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_20])).
% 8.06/2.85  tff(c_7695, plain, (![A_419]: (k5_relat_1(k6_partfun1(k2_relat_1(A_419)), k2_funct_1(A_419))=k2_funct_1(A_419) | ~v1_relat_1(k2_funct_1(A_419)) | ~v2_funct_1(A_419) | ~v1_funct_1(A_419) | ~v1_relat_1(A_419))), inference(superposition, [status(thm), theory('equality')], [c_230, c_102])).
% 8.06/2.85  tff(c_7719, plain, (k5_relat_1(k6_partfun1('#skF_3'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_356, c_7695])).
% 8.06/2.85  tff(c_7736, plain, (k5_relat_1(k6_partfun1('#skF_3'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_96, c_80, c_7719])).
% 8.06/2.85  tff(c_7739, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_7736])).
% 8.06/2.85  tff(c_7742, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_7739])).
% 8.06/2.85  tff(c_7746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_213, c_96, c_7742])).
% 8.06/2.85  tff(c_7748, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_7736])).
% 8.06/2.85  tff(c_86, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.06/2.85  tff(c_214, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_193])).
% 8.06/2.85  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.06/2.85  tff(c_117, plain, (![A_64]: (k1_xboole_0=A_64 | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.06/2.85  tff(c_121, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_117])).
% 8.06/2.85  tff(c_78, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.06/2.85  tff(c_124, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_121, c_78])).
% 8.06/2.85  tff(c_90, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.06/2.85  tff(c_88, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.06/2.85  tff(c_357, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_334])).
% 8.06/2.85  tff(c_70, plain, (![B_58, C_59, A_57]: (k6_partfun1(B_58)=k5_relat_1(k2_funct_1(C_59), C_59) | k1_xboole_0=B_58 | ~v2_funct_1(C_59) | k2_relset_1(A_57, B_58, C_59)!=B_58 | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~v1_funct_2(C_59, A_57, B_58) | ~v1_funct_1(C_59))), inference(cnfTransformation, [status(thm)], [f_204])).
% 8.06/2.85  tff(c_5523, plain, (![B_325, C_326, A_327]: (k6_partfun1(B_325)=k5_relat_1(k2_funct_1(C_326), C_326) | B_325='#skF_1' | ~v2_funct_1(C_326) | k2_relset_1(A_327, B_325, C_326)!=B_325 | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(A_327, B_325))) | ~v1_funct_2(C_326, A_327, B_325) | ~v1_funct_1(C_326))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_70])).
% 8.06/2.85  tff(c_5532, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_2') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_2', '#skF_5')!='#skF_2' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_5523])).
% 8.06/2.85  tff(c_5546, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_2') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5') | k2_relat_1('#skF_5')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_357, c_5532])).
% 8.06/2.85  tff(c_5547, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_5') | k2_relat_1('#skF_5')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_124, c_5546])).
% 8.06/2.85  tff(c_5574, plain, (k2_relat_1('#skF_5')!='#skF_2'), inference(splitLeft, [status(thm)], [c_5547])).
% 8.06/2.85  tff(c_94, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.06/2.85  tff(c_50, plain, (![A_32]: (m1_subset_1(k6_relat_1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.06/2.85  tff(c_97, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50])).
% 8.06/2.85  tff(c_315, plain, (![A_94, B_95, D_96]: (r2_relset_1(A_94, B_95, D_96, D_96) | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.06/2.85  tff(c_329, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_97, c_315])).
% 8.06/2.85  tff(c_5282, plain, (![C_315, D_316, E_318, B_314, F_317, A_313]: (k1_partfun1(A_313, B_314, C_315, D_316, E_318, F_317)=k5_relat_1(E_318, F_317) | ~m1_subset_1(F_317, k1_zfmisc_1(k2_zfmisc_1(C_315, D_316))) | ~v1_funct_1(F_317) | ~m1_subset_1(E_318, k1_zfmisc_1(k2_zfmisc_1(A_313, B_314))) | ~v1_funct_1(E_318))), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.06/2.85  tff(c_5291, plain, (![A_313, B_314, E_318]: (k1_partfun1(A_313, B_314, '#skF_3', '#skF_2', E_318, '#skF_5')=k5_relat_1(E_318, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_318, k1_zfmisc_1(k2_zfmisc_1(A_313, B_314))) | ~v1_funct_1(E_318))), inference(resolution, [status(thm)], [c_86, c_5282])).
% 8.06/2.85  tff(c_5575, plain, (![A_328, B_329, E_330]: (k1_partfun1(A_328, B_329, '#skF_3', '#skF_2', E_330, '#skF_5')=k5_relat_1(E_330, '#skF_5') | ~m1_subset_1(E_330, k1_zfmisc_1(k2_zfmisc_1(A_328, B_329))) | ~v1_funct_1(E_330))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_5291])).
% 8.06/2.85  tff(c_5585, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_5575])).
% 8.06/2.85  tff(c_5597, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_5585])).
% 8.06/2.85  tff(c_5750, plain, (![A_337, F_340, C_339, D_341, B_342, E_338]: (m1_subset_1(k1_partfun1(A_337, B_342, C_339, D_341, E_338, F_340), k1_zfmisc_1(k2_zfmisc_1(A_337, D_341))) | ~m1_subset_1(F_340, k1_zfmisc_1(k2_zfmisc_1(C_339, D_341))) | ~v1_funct_1(F_340) | ~m1_subset_1(E_338, k1_zfmisc_1(k2_zfmisc_1(A_337, B_342))) | ~v1_funct_1(E_338))), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.06/2.85  tff(c_5790, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5597, c_5750])).
% 8.06/2.85  tff(c_5808, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_90, c_86, c_5790])).
% 8.06/2.85  tff(c_82, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.06/2.85  tff(c_655, plain, (![D_122, C_123, A_124, B_125]: (D_122=C_123 | ~r2_relset_1(A_124, B_125, C_123, D_122) | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.06/2.85  tff(c_665, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_82, c_655])).
% 8.06/2.85  tff(c_684, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_665])).
% 8.06/2.85  tff(c_6041, plain, (k5_relat_1('#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5808, c_5597, c_5597, c_684])).
% 8.06/2.85  tff(c_6047, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6041, c_5597])).
% 8.06/2.85  tff(c_6173, plain, (![A_351, B_352, C_353, D_354]: (k2_relset_1(A_351, B_352, C_353)=B_352 | ~r2_relset_1(B_352, B_352, k1_partfun1(B_352, A_351, A_351, B_352, D_354, C_353), k6_partfun1(B_352)) | ~m1_subset_1(D_354, k1_zfmisc_1(k2_zfmisc_1(B_352, A_351))) | ~v1_funct_2(D_354, B_352, A_351) | ~v1_funct_1(D_354) | ~m1_subset_1(C_353, k1_zfmisc_1(k2_zfmisc_1(A_351, B_352))) | ~v1_funct_2(C_353, A_351, B_352) | ~v1_funct_1(C_353))), inference(cnfTransformation, [status(thm)], [f_162])).
% 8.06/2.85  tff(c_6176, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6047, c_6173])).
% 8.06/2.85  tff(c_6181, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_96, c_94, c_92, c_329, c_357, c_6176])).
% 8.06/2.85  tff(c_6183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5574, c_6181])).
% 8.06/2.85  tff(c_6185, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(splitRight, [status(thm)], [c_5547])).
% 8.06/2.85  tff(c_6, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.06/2.85  tff(c_8, plain, (![A_3]: (m1_subset_1(k2_subset_1(A_3), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.06/2.85  tff(c_105, plain, (![A_3]: (m1_subset_1(A_3, k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 8.06/2.85  tff(c_170, plain, (![A_74, B_75]: (r1_tarski(A_74, B_75) | ~m1_subset_1(A_74, k1_zfmisc_1(B_75)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.06/2.85  tff(c_190, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_105, c_170])).
% 8.06/2.85  tff(c_22, plain, (![B_16, A_15]: (k5_relat_1(B_16, k6_relat_1(A_15))=B_16 | ~r1_tarski(k2_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.06/2.85  tff(c_284, plain, (![B_91, A_92]: (k5_relat_1(B_91, k6_partfun1(A_92))=B_91 | ~r1_tarski(k2_relat_1(B_91), A_92) | ~v1_relat_1(B_91))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_22])).
% 8.06/2.85  tff(c_295, plain, (![B_91]: (k5_relat_1(B_91, k6_partfun1(k2_relat_1(B_91)))=B_91 | ~v1_relat_1(B_91))), inference(resolution, [status(thm)], [c_190, c_284])).
% 8.06/2.85  tff(c_6190, plain, (k5_relat_1('#skF_5', k6_partfun1('#skF_2'))='#skF_5' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6185, c_295])).
% 8.06/2.85  tff(c_6197, plain, (k5_relat_1('#skF_5', k6_partfun1('#skF_2'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_214, c_6190])).
% 8.06/2.85  tff(c_76, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.06/2.85  tff(c_123, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_121, c_76])).
% 8.06/2.85  tff(c_72, plain, (![A_57, C_59, B_58]: (k6_partfun1(A_57)=k5_relat_1(C_59, k2_funct_1(C_59)) | k1_xboole_0=B_58 | ~v2_funct_1(C_59) | k2_relset_1(A_57, B_58, C_59)!=B_58 | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~v1_funct_2(C_59, A_57, B_58) | ~v1_funct_1(C_59))), inference(cnfTransformation, [status(thm)], [f_204])).
% 8.06/2.85  tff(c_6992, plain, (![A_385, C_386, B_387]: (k6_partfun1(A_385)=k5_relat_1(C_386, k2_funct_1(C_386)) | B_387='#skF_1' | ~v2_funct_1(C_386) | k2_relset_1(A_385, B_387, C_386)!=B_387 | ~m1_subset_1(C_386, k1_zfmisc_1(k2_zfmisc_1(A_385, B_387))) | ~v1_funct_2(C_386, A_385, B_387) | ~v1_funct_1(C_386))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_72])).
% 8.06/2.85  tff(c_6999, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_6992])).
% 8.06/2.85  tff(c_7011, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_84, c_80, c_6999])).
% 8.06/2.85  tff(c_7012, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_123, c_7011])).
% 8.06/2.85  tff(c_6184, plain, (~v2_funct_1('#skF_5') | k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_5547])).
% 8.06/2.85  tff(c_6277, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_6184])).
% 8.06/2.85  tff(c_28, plain, (![A_18]: (v2_funct_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.06/2.85  tff(c_100, plain, (![A_18]: (v2_funct_1(k6_partfun1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_28])).
% 8.06/2.85  tff(c_6219, plain, (![A_355, B_356, E_357]: (k1_partfun1(A_355, B_356, '#skF_3', '#skF_2', E_357, '#skF_5')=k5_relat_1(E_357, '#skF_5') | ~m1_subset_1(E_357, k1_zfmisc_1(k2_zfmisc_1(A_355, B_356))) | ~v1_funct_1(E_357))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_5291])).
% 8.06/2.85  tff(c_6229, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_6219])).
% 8.06/2.85  tff(c_6241, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_6229])).
% 8.06/2.85  tff(c_6434, plain, (![C_364, F_365, D_366, B_367, A_362, E_363]: (m1_subset_1(k1_partfun1(A_362, B_367, C_364, D_366, E_363, F_365), k1_zfmisc_1(k2_zfmisc_1(A_362, D_366))) | ~m1_subset_1(F_365, k1_zfmisc_1(k2_zfmisc_1(C_364, D_366))) | ~v1_funct_1(F_365) | ~m1_subset_1(E_363, k1_zfmisc_1(k2_zfmisc_1(A_362, B_367))) | ~v1_funct_1(E_363))), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.06/2.85  tff(c_6465, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6241, c_6434])).
% 8.06/2.85  tff(c_6478, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_90, c_86, c_6465])).
% 8.06/2.85  tff(c_6785, plain, (k5_relat_1('#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6478, c_6241, c_6241, c_684])).
% 8.06/2.85  tff(c_6792, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6785, c_6241])).
% 8.06/2.85  tff(c_64, plain, (![B_52, C_53, D_54, A_51, E_56]: (k1_xboole_0=C_53 | v2_funct_1(E_56) | k2_relset_1(A_51, B_52, D_54)!=B_52 | ~v2_funct_1(k1_partfun1(A_51, B_52, B_52, C_53, D_54, E_56)) | ~m1_subset_1(E_56, k1_zfmisc_1(k2_zfmisc_1(B_52, C_53))) | ~v1_funct_2(E_56, B_52, C_53) | ~v1_funct_1(E_56) | ~m1_subset_1(D_54, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))) | ~v1_funct_2(D_54, A_51, B_52) | ~v1_funct_1(D_54))), inference(cnfTransformation, [status(thm)], [f_188])).
% 8.06/2.85  tff(c_6885, plain, (![B_52, C_53, D_54, A_51, E_56]: (C_53='#skF_1' | v2_funct_1(E_56) | k2_relset_1(A_51, B_52, D_54)!=B_52 | ~v2_funct_1(k1_partfun1(A_51, B_52, B_52, C_53, D_54, E_56)) | ~m1_subset_1(E_56, k1_zfmisc_1(k2_zfmisc_1(B_52, C_53))) | ~v1_funct_2(E_56, B_52, C_53) | ~v1_funct_1(E_56) | ~m1_subset_1(D_54, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))) | ~v1_funct_2(D_54, A_51, B_52) | ~v1_funct_1(D_54))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_64])).
% 8.06/2.85  tff(c_6894, plain, ('#skF_2'='#skF_1' | v2_funct_1('#skF_5') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6792, c_6885])).
% 8.06/2.85  tff(c_6901, plain, ('#skF_2'='#skF_1' | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_92, c_90, c_88, c_86, c_100, c_84, c_6894])).
% 8.06/2.85  tff(c_6903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6277, c_124, c_6901])).
% 8.06/2.85  tff(c_6905, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_6184])).
% 8.06/2.85  tff(c_7713, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_5'))=k2_funct_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6185, c_7695])).
% 8.06/2.85  tff(c_7734, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_5'))=k2_funct_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_90, c_6905, c_7713])).
% 8.06/2.85  tff(c_7774, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_7734])).
% 8.06/2.85  tff(c_7777, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_7774])).
% 8.06/2.85  tff(c_7781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_214, c_90, c_7777])).
% 8.06/2.85  tff(c_7783, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_7734])).
% 8.06/2.85  tff(c_362, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_3'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_356, c_295])).
% 8.06/2.85  tff(c_369, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_213, c_362])).
% 8.06/2.85  tff(c_6186, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6185, c_357])).
% 8.06/2.85  tff(c_7001, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_2', '#skF_5')!='#skF_2' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_6992])).
% 8.06/2.85  tff(c_7015, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_6186, c_6905, c_7001])).
% 8.06/2.85  tff(c_7016, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_124, c_7015])).
% 8.06/2.85  tff(c_7122, plain, (![F_391, D_392, B_393, E_389, C_390, A_388]: (m1_subset_1(k1_partfun1(A_388, B_393, C_390, D_392, E_389, F_391), k1_zfmisc_1(k2_zfmisc_1(A_388, D_392))) | ~m1_subset_1(F_391, k1_zfmisc_1(k2_zfmisc_1(C_390, D_392))) | ~v1_funct_1(F_391) | ~m1_subset_1(E_389, k1_zfmisc_1(k2_zfmisc_1(A_388, B_393))) | ~v1_funct_1(E_389))), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.06/2.85  tff(c_7156, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6241, c_7122])).
% 8.06/2.85  tff(c_7171, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_90, c_86, c_7156])).
% 8.06/2.85  tff(c_7606, plain, (k5_relat_1('#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7171, c_6241, c_6241, c_684])).
% 8.06/2.85  tff(c_14, plain, (![A_6, B_10, C_12]: (k5_relat_1(k5_relat_1(A_6, B_10), C_12)=k5_relat_1(A_6, k5_relat_1(B_10, C_12)) | ~v1_relat_1(C_12) | ~v1_relat_1(B_10) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.06/2.85  tff(c_7625, plain, (![C_12]: (k5_relat_1(k6_partfun1('#skF_2'), C_12)=k5_relat_1('#skF_4', k5_relat_1('#skF_5', C_12)) | ~v1_relat_1(C_12) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7606, c_14])).
% 8.06/2.85  tff(c_7937, plain, (![C_423]: (k5_relat_1(k6_partfun1('#skF_2'), C_423)=k5_relat_1('#skF_4', k5_relat_1('#skF_5', C_423)) | ~v1_relat_1(C_423))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_214, c_7625])).
% 8.06/2.85  tff(c_7782, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_5'))=k2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_7734])).
% 8.06/2.85  tff(c_7946, plain, (k5_relat_1('#skF_4', k5_relat_1('#skF_5', k2_funct_1('#skF_5')))=k2_funct_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7937, c_7782])).
% 8.06/2.85  tff(c_8018, plain, (k2_funct_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7783, c_369, c_7016, c_7946])).
% 8.06/2.85  tff(c_8052, plain, (k5_relat_1('#skF_5', '#skF_4')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8018, c_7016])).
% 8.06/2.85  tff(c_8174, plain, (![C_12]: (k5_relat_1(k6_partfun1('#skF_3'), C_12)=k5_relat_1('#skF_5', k5_relat_1('#skF_4', C_12)) | ~v1_relat_1(C_12) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8052, c_14])).
% 8.06/2.85  tff(c_8506, plain, (![C_439]: (k5_relat_1(k6_partfun1('#skF_3'), C_439)=k5_relat_1('#skF_5', k5_relat_1('#skF_4', C_439)) | ~v1_relat_1(C_439))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_213, c_8174])).
% 8.06/2.85  tff(c_7747, plain, (k5_relat_1(k6_partfun1('#skF_3'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_7736])).
% 8.06/2.85  tff(c_8519, plain, (k5_relat_1('#skF_5', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8506, c_7747])).
% 8.06/2.85  tff(c_8599, plain, (k2_funct_1('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7748, c_6197, c_7012, c_8519])).
% 8.06/2.85  tff(c_8601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_8599])).
% 8.06/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.06/2.85  
% 8.06/2.85  Inference rules
% 8.06/2.85  ----------------------
% 8.06/2.85  #Ref     : 0
% 8.06/2.85  #Sup     : 1811
% 8.06/2.85  #Fact    : 0
% 8.06/2.85  #Define  : 0
% 8.06/2.85  #Split   : 28
% 8.06/2.85  #Chain   : 0
% 8.06/2.85  #Close   : 0
% 8.06/2.85  
% 8.06/2.85  Ordering : KBO
% 8.06/2.85  
% 8.06/2.85  Simplification rules
% 8.06/2.85  ----------------------
% 8.06/2.85  #Subsume      : 57
% 8.06/2.85  #Demod        : 2837
% 8.06/2.85  #Tautology    : 862
% 8.06/2.85  #SimpNegUnit  : 86
% 8.06/2.85  #BackRed      : 110
% 8.06/2.85  
% 8.06/2.85  #Partial instantiations: 0
% 8.06/2.85  #Strategies tried      : 1
% 8.06/2.85  
% 8.06/2.85  Timing (in seconds)
% 8.06/2.85  ----------------------
% 8.06/2.85  Preprocessing        : 0.40
% 8.06/2.85  Parsing              : 0.21
% 8.06/2.85  CNF conversion       : 0.03
% 8.06/2.85  Main loop            : 1.58
% 8.06/2.85  Inferencing          : 0.50
% 8.06/2.85  Reduction            : 0.64
% 8.06/2.85  Demodulation         : 0.48
% 8.06/2.85  BG Simplification    : 0.06
% 8.06/2.85  Subsumption          : 0.26
% 8.06/2.85  Abstraction          : 0.08
% 8.06/2.85  MUC search           : 0.00
% 8.06/2.85  Cooper               : 0.00
% 8.06/2.85  Total                : 2.04
% 8.06/2.85  Index Insertion      : 0.00
% 8.06/2.85  Index Deletion       : 0.00
% 8.06/2.85  Index Matching       : 0.00
% 8.06/2.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
