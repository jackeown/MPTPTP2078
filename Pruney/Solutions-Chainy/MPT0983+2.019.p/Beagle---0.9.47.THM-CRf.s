%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:03 EST 2020

% Result     : Theorem 5.66s
% Output     : CNFRefutation 5.82s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 293 expanded)
%              Number of leaves         :   43 ( 126 expanded)
%              Depth                    :   10
%              Number of atoms          :  214 ( 994 expanded)
%              Number of equality atoms :   30 (  79 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_169,negated_conjecture,(
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

tff(f_110,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_66,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_149,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_127,axiom,(
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

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_56,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_106,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_48,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_24,plain,(
    ! [A_13] : v2_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_71,plain,(
    ! [A_13] : v2_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_24])).

tff(c_1481,plain,(
    ! [D_303,E_308,C_307,F_306,B_304,A_305] :
      ( m1_subset_1(k1_partfun1(A_305,B_304,C_307,D_303,E_308,F_306),k1_zfmisc_1(k2_zfmisc_1(A_305,D_303)))
      | ~ m1_subset_1(F_306,k1_zfmisc_1(k2_zfmisc_1(C_307,D_303)))
      | ~ v1_funct_1(F_306)
      | ~ m1_subset_1(E_308,k1_zfmisc_1(k2_zfmisc_1(A_305,B_304)))
      | ~ v1_funct_1(E_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1316,plain,(
    ! [D_273,C_274,A_275,B_276] :
      ( D_273 = C_274
      | ~ r2_relset_1(A_275,B_276,C_274,D_273)
      | ~ m1_subset_1(D_273,k1_zfmisc_1(k2_zfmisc_1(A_275,B_276)))
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(A_275,B_276))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1324,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_1316])).

tff(c_1339,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1324])).

tff(c_1358,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1339])).

tff(c_1492,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1481,c_1358])).

tff(c_1522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_1492])).

tff(c_1523,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1339])).

tff(c_1755,plain,(
    ! [B_361,E_360,A_359,D_363,C_362] :
      ( k1_xboole_0 = C_362
      | v2_funct_1(D_363)
      | ~ v2_funct_1(k1_partfun1(A_359,B_361,B_361,C_362,D_363,E_360))
      | ~ m1_subset_1(E_360,k1_zfmisc_1(k2_zfmisc_1(B_361,C_362)))
      | ~ v1_funct_2(E_360,B_361,C_362)
      | ~ v1_funct_1(E_360)
      | ~ m1_subset_1(D_363,k1_zfmisc_1(k2_zfmisc_1(A_359,B_361)))
      | ~ v1_funct_2(D_363,A_359,B_361)
      | ~ v1_funct_1(D_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1757,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1523,c_1755])).

tff(c_1762,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_71,c_1757])).

tff(c_1763,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_1762])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1797,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1763,c_2])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1795,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1763,c_1763,c_8])).

tff(c_14,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_140,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_149,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_140])).

tff(c_161,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_149])).

tff(c_165,plain,(
    ! [A_59] :
      ( v2_funct_1(A_59)
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59)
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_168,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_165,c_106])).

tff(c_171,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_168])).

tff(c_174,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_171])).

tff(c_176,plain,(
    ! [B_61,A_62] :
      ( v1_xboole_0(B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62))
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_185,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_176])).

tff(c_195,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_185])).

tff(c_1882,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1795,c_195])).

tff(c_1886,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1797,c_1882])).

tff(c_1887,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1961,plain,(
    ! [B_382,A_383] :
      ( v1_relat_1(B_382)
      | ~ m1_subset_1(B_382,k1_zfmisc_1(A_383))
      | ~ v1_relat_1(A_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1970,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_1961])).

tff(c_1982,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1970])).

tff(c_2007,plain,(
    ! [C_388,B_389,A_390] :
      ( v5_relat_1(C_388,B_389)
      | ~ m1_subset_1(C_388,k1_zfmisc_1(k2_zfmisc_1(A_390,B_389))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2024,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_2007])).

tff(c_2045,plain,(
    ! [A_398,B_399,D_400] :
      ( r2_relset_1(A_398,B_399,D_400,D_400)
      | ~ m1_subset_1(D_400,k1_zfmisc_1(k2_zfmisc_1(A_398,B_399))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2056,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_46,c_2045])).

tff(c_2098,plain,(
    ! [A_407,B_408,C_409] :
      ( k2_relset_1(A_407,B_408,C_409) = k2_relat_1(C_409)
      | ~ m1_subset_1(C_409,k1_zfmisc_1(k2_zfmisc_1(A_407,B_408))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2115,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_2098])).

tff(c_40,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] :
      ( m1_subset_1(k1_partfun1(A_26,B_27,C_28,D_29,E_30,F_31),k1_zfmisc_1(k2_zfmisc_1(A_26,D_29)))
      | ~ m1_subset_1(F_31,k1_zfmisc_1(k2_zfmisc_1(C_28,D_29)))
      | ~ v1_funct_1(F_31)
      | ~ m1_subset_1(E_30,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_1(E_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2126,plain,(
    ! [D_411,C_412,A_413,B_414] :
      ( D_411 = C_412
      | ~ r2_relset_1(A_413,B_414,C_412,D_411)
      | ~ m1_subset_1(D_411,k1_zfmisc_1(k2_zfmisc_1(A_413,B_414)))
      | ~ m1_subset_1(C_412,k1_zfmisc_1(k2_zfmisc_1(A_413,B_414))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2134,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_2126])).

tff(c_2149,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2134])).

tff(c_2381,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2149])).

tff(c_2385,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_2381])).

tff(c_2389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_2385])).

tff(c_2390,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2149])).

tff(c_2468,plain,(
    ! [A_495,B_496,C_497,D_498] :
      ( k2_relset_1(A_495,B_496,C_497) = B_496
      | ~ r2_relset_1(B_496,B_496,k1_partfun1(B_496,A_495,A_495,B_496,D_498,C_497),k6_partfun1(B_496))
      | ~ m1_subset_1(D_498,k1_zfmisc_1(k2_zfmisc_1(B_496,A_495)))
      | ~ v1_funct_2(D_498,B_496,A_495)
      | ~ v1_funct_1(D_498)
      | ~ m1_subset_1(C_497,k1_zfmisc_1(k2_zfmisc_1(A_495,B_496)))
      | ~ v1_funct_2(C_497,A_495,B_496)
      | ~ v1_funct_1(C_497) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2471,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2390,c_2468])).

tff(c_2473,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_2056,c_2115,c_2471])).

tff(c_36,plain,(
    ! [B_25] :
      ( v2_funct_2(B_25,k2_relat_1(B_25))
      | ~ v5_relat_1(B_25,k2_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2478,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2473,c_36])).

tff(c_2482,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1982,c_2024,c_2473,c_2478])).

tff(c_2484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1887,c_2482])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.66/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.11  
% 5.76/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.11  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.76/2.11  
% 5.76/2.11  %Foreground sorts:
% 5.76/2.11  
% 5.76/2.11  
% 5.76/2.11  %Background operators:
% 5.76/2.11  
% 5.76/2.11  
% 5.76/2.11  %Foreground operators:
% 5.76/2.11  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.76/2.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.76/2.11  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.76/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.76/2.11  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.76/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.76/2.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.76/2.11  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.76/2.11  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.76/2.11  tff('#skF_2', type, '#skF_2': $i).
% 5.76/2.11  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.76/2.11  tff('#skF_3', type, '#skF_3': $i).
% 5.76/2.11  tff('#skF_1', type, '#skF_1': $i).
% 5.76/2.11  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.76/2.11  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.76/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.76/2.11  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.76/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.76/2.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.76/2.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.76/2.11  tff('#skF_4', type, '#skF_4': $i).
% 5.76/2.11  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.76/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.76/2.11  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.76/2.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.76/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.76/2.11  
% 5.82/2.13  tff(f_169, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 5.82/2.13  tff(f_110, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.82/2.13  tff(f_66, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 5.82/2.13  tff(f_104, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.82/2.13  tff(f_108, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.82/2.13  tff(f_84, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.82/2.13  tff(f_149, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 5.82/2.13  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.82/2.13  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.82/2.13  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.82/2.13  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.82/2.13  tff(f_64, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_1)).
% 5.82/2.13  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.82/2.13  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.82/2.13  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.82/2.13  tff(f_127, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 5.82/2.13  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.82/2.13  tff(c_56, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.82/2.13  tff(c_106, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 5.82/2.13  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.82/2.13  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.82/2.13  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.82/2.13  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.82/2.13  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.82/2.13  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.82/2.13  tff(c_48, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.82/2.13  tff(c_24, plain, (![A_13]: (v2_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.82/2.13  tff(c_71, plain, (![A_13]: (v2_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_24])).
% 5.82/2.13  tff(c_1481, plain, (![D_303, E_308, C_307, F_306, B_304, A_305]: (m1_subset_1(k1_partfun1(A_305, B_304, C_307, D_303, E_308, F_306), k1_zfmisc_1(k2_zfmisc_1(A_305, D_303))) | ~m1_subset_1(F_306, k1_zfmisc_1(k2_zfmisc_1(C_307, D_303))) | ~v1_funct_1(F_306) | ~m1_subset_1(E_308, k1_zfmisc_1(k2_zfmisc_1(A_305, B_304))) | ~v1_funct_1(E_308))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.82/2.13  tff(c_46, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.82/2.13  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.82/2.13  tff(c_1316, plain, (![D_273, C_274, A_275, B_276]: (D_273=C_274 | ~r2_relset_1(A_275, B_276, C_274, D_273) | ~m1_subset_1(D_273, k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.82/2.13  tff(c_1324, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_1316])).
% 5.82/2.13  tff(c_1339, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1324])).
% 5.82/2.13  tff(c_1358, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1339])).
% 5.82/2.13  tff(c_1492, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1481, c_1358])).
% 5.82/2.13  tff(c_1522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_1492])).
% 5.82/2.13  tff(c_1523, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1339])).
% 5.82/2.13  tff(c_1755, plain, (![B_361, E_360, A_359, D_363, C_362]: (k1_xboole_0=C_362 | v2_funct_1(D_363) | ~v2_funct_1(k1_partfun1(A_359, B_361, B_361, C_362, D_363, E_360)) | ~m1_subset_1(E_360, k1_zfmisc_1(k2_zfmisc_1(B_361, C_362))) | ~v1_funct_2(E_360, B_361, C_362) | ~v1_funct_1(E_360) | ~m1_subset_1(D_363, k1_zfmisc_1(k2_zfmisc_1(A_359, B_361))) | ~v1_funct_2(D_363, A_359, B_361) | ~v1_funct_1(D_363))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.82/2.13  tff(c_1757, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1523, c_1755])).
% 5.82/2.13  tff(c_1762, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_71, c_1757])).
% 5.82/2.13  tff(c_1763, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_106, c_1762])).
% 5.82/2.13  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.82/2.13  tff(c_1797, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1763, c_2])).
% 5.82/2.13  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.82/2.13  tff(c_1795, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1763, c_1763, c_8])).
% 5.82/2.13  tff(c_14, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.82/2.13  tff(c_140, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.82/2.13  tff(c_149, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_140])).
% 5.82/2.13  tff(c_161, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_149])).
% 5.82/2.13  tff(c_165, plain, (![A_59]: (v2_funct_1(A_59) | ~v1_funct_1(A_59) | ~v1_relat_1(A_59) | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.82/2.13  tff(c_168, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_165, c_106])).
% 5.82/2.13  tff(c_171, plain, (~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_168])).
% 5.82/2.13  tff(c_174, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_171])).
% 5.82/2.13  tff(c_176, plain, (![B_61, A_62]: (v1_xboole_0(B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)) | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.82/2.13  tff(c_185, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_176])).
% 5.82/2.13  tff(c_195, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_174, c_185])).
% 5.82/2.13  tff(c_1882, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1795, c_195])).
% 5.82/2.13  tff(c_1886, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1797, c_1882])).
% 5.82/2.13  tff(c_1887, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 5.82/2.13  tff(c_1961, plain, (![B_382, A_383]: (v1_relat_1(B_382) | ~m1_subset_1(B_382, k1_zfmisc_1(A_383)) | ~v1_relat_1(A_383))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.82/2.13  tff(c_1970, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_1961])).
% 5.82/2.13  tff(c_1982, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1970])).
% 5.82/2.13  tff(c_2007, plain, (![C_388, B_389, A_390]: (v5_relat_1(C_388, B_389) | ~m1_subset_1(C_388, k1_zfmisc_1(k2_zfmisc_1(A_390, B_389))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.82/2.13  tff(c_2024, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_2007])).
% 5.82/2.13  tff(c_2045, plain, (![A_398, B_399, D_400]: (r2_relset_1(A_398, B_399, D_400, D_400) | ~m1_subset_1(D_400, k1_zfmisc_1(k2_zfmisc_1(A_398, B_399))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.82/2.13  tff(c_2056, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_46, c_2045])).
% 5.82/2.13  tff(c_2098, plain, (![A_407, B_408, C_409]: (k2_relset_1(A_407, B_408, C_409)=k2_relat_1(C_409) | ~m1_subset_1(C_409, k1_zfmisc_1(k2_zfmisc_1(A_407, B_408))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.82/2.13  tff(c_2115, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_2098])).
% 5.82/2.13  tff(c_40, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (m1_subset_1(k1_partfun1(A_26, B_27, C_28, D_29, E_30, F_31), k1_zfmisc_1(k2_zfmisc_1(A_26, D_29))) | ~m1_subset_1(F_31, k1_zfmisc_1(k2_zfmisc_1(C_28, D_29))) | ~v1_funct_1(F_31) | ~m1_subset_1(E_30, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_1(E_30))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.82/2.13  tff(c_2126, plain, (![D_411, C_412, A_413, B_414]: (D_411=C_412 | ~r2_relset_1(A_413, B_414, C_412, D_411) | ~m1_subset_1(D_411, k1_zfmisc_1(k2_zfmisc_1(A_413, B_414))) | ~m1_subset_1(C_412, k1_zfmisc_1(k2_zfmisc_1(A_413, B_414))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.82/2.13  tff(c_2134, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_2126])).
% 5.82/2.13  tff(c_2149, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2134])).
% 5.82/2.13  tff(c_2381, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2149])).
% 5.82/2.13  tff(c_2385, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_2381])).
% 5.82/2.13  tff(c_2389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_2385])).
% 5.82/2.13  tff(c_2390, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2149])).
% 5.82/2.13  tff(c_2468, plain, (![A_495, B_496, C_497, D_498]: (k2_relset_1(A_495, B_496, C_497)=B_496 | ~r2_relset_1(B_496, B_496, k1_partfun1(B_496, A_495, A_495, B_496, D_498, C_497), k6_partfun1(B_496)) | ~m1_subset_1(D_498, k1_zfmisc_1(k2_zfmisc_1(B_496, A_495))) | ~v1_funct_2(D_498, B_496, A_495) | ~v1_funct_1(D_498) | ~m1_subset_1(C_497, k1_zfmisc_1(k2_zfmisc_1(A_495, B_496))) | ~v1_funct_2(C_497, A_495, B_496) | ~v1_funct_1(C_497))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.82/2.13  tff(c_2471, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2390, c_2468])).
% 5.82/2.13  tff(c_2473, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_2056, c_2115, c_2471])).
% 5.82/2.13  tff(c_36, plain, (![B_25]: (v2_funct_2(B_25, k2_relat_1(B_25)) | ~v5_relat_1(B_25, k2_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.82/2.13  tff(c_2478, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2473, c_36])).
% 5.82/2.13  tff(c_2482, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1982, c_2024, c_2473, c_2478])).
% 5.82/2.13  tff(c_2484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1887, c_2482])).
% 5.82/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.82/2.13  
% 5.82/2.13  Inference rules
% 5.82/2.13  ----------------------
% 5.82/2.13  #Ref     : 0
% 5.82/2.13  #Sup     : 507
% 5.82/2.13  #Fact    : 0
% 5.82/2.13  #Define  : 0
% 5.82/2.13  #Split   : 13
% 5.82/2.13  #Chain   : 0
% 5.82/2.13  #Close   : 0
% 5.82/2.13  
% 5.82/2.13  Ordering : KBO
% 5.82/2.13  
% 5.82/2.13  Simplification rules
% 5.82/2.13  ----------------------
% 5.82/2.13  #Subsume      : 7
% 5.82/2.13  #Demod        : 495
% 5.82/2.13  #Tautology    : 176
% 5.82/2.13  #SimpNegUnit  : 6
% 5.82/2.13  #BackRed      : 117
% 5.82/2.13  
% 5.82/2.13  #Partial instantiations: 0
% 5.82/2.13  #Strategies tried      : 1
% 5.82/2.13  
% 5.82/2.13  Timing (in seconds)
% 5.82/2.13  ----------------------
% 5.82/2.14  Preprocessing        : 0.39
% 5.82/2.14  Parsing              : 0.20
% 5.82/2.14  CNF conversion       : 0.03
% 5.82/2.14  Main loop            : 0.94
% 5.82/2.14  Inferencing          : 0.34
% 5.82/2.14  Reduction            : 0.33
% 5.82/2.14  Demodulation         : 0.24
% 5.82/2.14  BG Simplification    : 0.04
% 5.82/2.14  Subsumption          : 0.15
% 5.82/2.14  Abstraction          : 0.04
% 5.82/2.14  MUC search           : 0.00
% 5.82/2.14  Cooper               : 0.00
% 5.82/2.14  Total                : 1.38
% 5.82/2.14  Index Insertion      : 0.00
% 5.82/2.14  Index Deletion       : 0.00
% 5.82/2.14  Index Matching       : 0.00
% 5.82/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
