%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:11 EST 2020

% Result     : Theorem 5.26s
% Output     : CNFRefutation 5.26s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 409 expanded)
%              Number of leaves         :   44 ( 164 expanded)
%              Depth                    :    9
%              Number of atoms          :  278 (1315 expanded)
%              Number of equality atoms :   51 ( 155 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_171,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_134,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_48,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_132,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_102,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_122,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_151,axiom,(
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

tff(f_110,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_110,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_122,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_110])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_121,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_110])).

tff(c_143,plain,(
    ! [C_69,A_70,B_71] :
      ( v4_relat_1(C_69,A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_156,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_143])).

tff(c_48,plain,(
    ! [A_44] : k6_relat_1(A_44) = k6_partfun1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_14,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_70,plain,(
    ! [A_8] : k1_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_14])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1465,plain,(
    ! [A_285,C_289,B_286,D_290,E_287,F_288] :
      ( k1_partfun1(A_285,B_286,C_289,D_290,E_287,F_288) = k5_relat_1(E_287,F_288)
      | ~ m1_subset_1(F_288,k1_zfmisc_1(k2_zfmisc_1(C_289,D_290)))
      | ~ v1_funct_1(F_288)
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286)))
      | ~ v1_funct_1(E_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1469,plain,(
    ! [A_285,B_286,E_287] :
      ( k1_partfun1(A_285,B_286,'#skF_2','#skF_1',E_287,'#skF_4') = k5_relat_1(E_287,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286)))
      | ~ v1_funct_1(E_287) ) ),
    inference(resolution,[status(thm)],[c_56,c_1465])).

tff(c_1479,plain,(
    ! [A_291,B_292,E_293] :
      ( k1_partfun1(A_291,B_292,'#skF_2','#skF_1',E_293,'#skF_4') = k5_relat_1(E_293,'#skF_4')
      | ~ m1_subset_1(E_293,k1_zfmisc_1(k2_zfmisc_1(A_291,B_292)))
      | ~ v1_funct_1(E_293) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1469])).

tff(c_1488,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1479])).

tff(c_1495,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1488])).

tff(c_36,plain,(
    ! [A_29] : m1_subset_1(k6_relat_1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_67,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36])).

tff(c_54,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1350,plain,(
    ! [D_254,C_255,A_256,B_257] :
      ( D_254 = C_255
      | ~ r2_relset_1(A_256,B_257,C_255,D_254)
      | ~ m1_subset_1(D_254,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257)))
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1358,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_54,c_1350])).

tff(c_1373,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_1358])).

tff(c_1384,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1373])).

tff(c_1502,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_1384])).

tff(c_1514,plain,(
    ! [F_297,B_296,A_299,D_300,E_295,C_298] :
      ( m1_subset_1(k1_partfun1(A_299,B_296,C_298,D_300,E_295,F_297),k1_zfmisc_1(k2_zfmisc_1(A_299,D_300)))
      | ~ m1_subset_1(F_297,k1_zfmisc_1(k2_zfmisc_1(C_298,D_300)))
      | ~ v1_funct_1(F_297)
      | ~ m1_subset_1(E_295,k1_zfmisc_1(k2_zfmisc_1(A_299,B_296)))
      | ~ v1_funct_1(E_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1544,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1495,c_1514])).

tff(c_1559,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_1544])).

tff(c_1561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1502,c_1559])).

tff(c_1562,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1373])).

tff(c_1671,plain,(
    ! [B_330,E_331,A_329,C_333,F_332,D_334] :
      ( k1_partfun1(A_329,B_330,C_333,D_334,E_331,F_332) = k5_relat_1(E_331,F_332)
      | ~ m1_subset_1(F_332,k1_zfmisc_1(k2_zfmisc_1(C_333,D_334)))
      | ~ v1_funct_1(F_332)
      | ~ m1_subset_1(E_331,k1_zfmisc_1(k2_zfmisc_1(A_329,B_330)))
      | ~ v1_funct_1(E_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1675,plain,(
    ! [A_329,B_330,E_331] :
      ( k1_partfun1(A_329,B_330,'#skF_2','#skF_1',E_331,'#skF_4') = k5_relat_1(E_331,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_331,k1_zfmisc_1(k2_zfmisc_1(A_329,B_330)))
      | ~ v1_funct_1(E_331) ) ),
    inference(resolution,[status(thm)],[c_56,c_1671])).

tff(c_1685,plain,(
    ! [A_335,B_336,E_337] :
      ( k1_partfun1(A_335,B_336,'#skF_2','#skF_1',E_337,'#skF_4') = k5_relat_1(E_337,'#skF_4')
      | ~ m1_subset_1(E_337,k1_zfmisc_1(k2_zfmisc_1(A_335,B_336)))
      | ~ v1_funct_1(E_337) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1675])).

tff(c_1694,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1685])).

tff(c_1701,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1562,c_1694])).

tff(c_12,plain,(
    ! [A_5,B_7] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_5,B_7)),k1_relat_1(A_5))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_157,plain,(
    ! [B_72,A_73] :
      ( r1_tarski(k1_relat_1(B_72),A_73)
      | ~ v4_relat_1(B_72,A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1160,plain,(
    ! [B_231,A_232] :
      ( k1_relat_1(B_231) = A_232
      | ~ r1_tarski(A_232,k1_relat_1(B_231))
      | ~ v4_relat_1(B_231,A_232)
      | ~ v1_relat_1(B_231) ) ),
    inference(resolution,[status(thm)],[c_157,c_2])).

tff(c_1180,plain,(
    ! [A_5,B_7] :
      ( k1_relat_1(k5_relat_1(A_5,B_7)) = k1_relat_1(A_5)
      | ~ v4_relat_1(A_5,k1_relat_1(k5_relat_1(A_5,B_7)))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_1160])).

tff(c_1711,plain,
    ( k1_relat_1(k5_relat_1('#skF_3','#skF_4')) = k1_relat_1('#skF_3')
    | ~ v4_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1')))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1701,c_1180])).

tff(c_1726,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_121,c_156,c_70,c_70,c_1701,c_1711])).

tff(c_52,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_101,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_22,plain,(
    ! [A_15] : v2_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_68,plain,(
    ! [A_15] : v2_funct_1(k6_partfun1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_22])).

tff(c_1213,plain,(
    ! [B_239,A_240] :
      ( r1_tarski(k2_relat_1(B_239),k1_relat_1(A_240))
      | k1_relat_1(k5_relat_1(B_239,A_240)) != k1_relat_1(B_239)
      | ~ v1_funct_1(B_239)
      | ~ v1_relat_1(B_239)
      | ~ v1_funct_1(A_240)
      | ~ v1_relat_1(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [B_14,A_12] :
      ( v2_funct_1(B_14)
      | ~ r1_tarski(k2_relat_1(B_14),k1_relat_1(A_12))
      | ~ v2_funct_1(k5_relat_1(B_14,A_12))
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1232,plain,(
    ! [B_239,A_240] :
      ( v2_funct_1(B_239)
      | ~ v2_funct_1(k5_relat_1(B_239,A_240))
      | k1_relat_1(k5_relat_1(B_239,A_240)) != k1_relat_1(B_239)
      | ~ v1_funct_1(B_239)
      | ~ v1_relat_1(B_239)
      | ~ v1_funct_1(A_240)
      | ~ v1_relat_1(A_240) ) ),
    inference(resolution,[status(thm)],[c_1213,c_20])).

tff(c_1705,plain,
    ( v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | k1_relat_1(k5_relat_1('#skF_3','#skF_4')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1701,c_1232])).

tff(c_1721,plain,
    ( v2_funct_1('#skF_3')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_60,c_122,c_66,c_70,c_1701,c_68,c_1705])).

tff(c_1722,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_1721])).

tff(c_1811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1726,c_1722])).

tff(c_1812,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1822,plain,(
    ! [C_341,A_342,B_343] :
      ( v1_relat_1(C_341)
      | ~ m1_subset_1(C_341,k1_zfmisc_1(k2_zfmisc_1(A_342,B_343))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1833,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_1822])).

tff(c_1869,plain,(
    ! [C_354,B_355,A_356] :
      ( v5_relat_1(C_354,B_355)
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(A_356,B_355))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1880,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_1869])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_64,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1961,plain,(
    ! [A_370,B_371,D_372] :
      ( r2_relset_1(A_370,B_371,D_372,D_372)
      | ~ m1_subset_1(D_372,k1_zfmisc_1(k2_zfmisc_1(A_370,B_371))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1968,plain,(
    ! [A_29] : r2_relset_1(A_29,A_29,k6_partfun1(A_29),k6_partfun1(A_29)) ),
    inference(resolution,[status(thm)],[c_67,c_1961])).

tff(c_1972,plain,(
    ! [A_374,B_375,C_376] :
      ( k2_relset_1(A_374,B_375,C_376) = k2_relat_1(C_376)
      | ~ m1_subset_1(C_376,k1_zfmisc_1(k2_zfmisc_1(A_374,B_375))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1984,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_1972])).

tff(c_2263,plain,(
    ! [A_424,F_427,B_425,C_428,D_429,E_426] :
      ( k1_partfun1(A_424,B_425,C_428,D_429,E_426,F_427) = k5_relat_1(E_426,F_427)
      | ~ m1_subset_1(F_427,k1_zfmisc_1(k2_zfmisc_1(C_428,D_429)))
      | ~ v1_funct_1(F_427)
      | ~ m1_subset_1(E_426,k1_zfmisc_1(k2_zfmisc_1(A_424,B_425)))
      | ~ v1_funct_1(E_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2267,plain,(
    ! [A_424,B_425,E_426] :
      ( k1_partfun1(A_424,B_425,'#skF_2','#skF_1',E_426,'#skF_4') = k5_relat_1(E_426,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_426,k1_zfmisc_1(k2_zfmisc_1(A_424,B_425)))
      | ~ v1_funct_1(E_426) ) ),
    inference(resolution,[status(thm)],[c_56,c_2263])).

tff(c_2278,plain,(
    ! [A_432,B_433,E_434] :
      ( k1_partfun1(A_432,B_433,'#skF_2','#skF_1',E_434,'#skF_4') = k5_relat_1(E_434,'#skF_4')
      | ~ m1_subset_1(E_434,k1_zfmisc_1(k2_zfmisc_1(A_432,B_433)))
      | ~ v1_funct_1(E_434) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2267])).

tff(c_2287,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2278])).

tff(c_2294,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2287])).

tff(c_2072,plain,(
    ! [D_390,C_391,A_392,B_393] :
      ( D_390 = C_391
      | ~ r2_relset_1(A_392,B_393,C_391,D_390)
      | ~ m1_subset_1(D_390,k1_zfmisc_1(k2_zfmisc_1(A_392,B_393)))
      | ~ m1_subset_1(C_391,k1_zfmisc_1(k2_zfmisc_1(A_392,B_393))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2080,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_54,c_2072])).

tff(c_2095,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_2080])).

tff(c_2164,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2095])).

tff(c_2301,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2294,c_2164])).

tff(c_2312,plain,(
    ! [E_435,F_437,B_436,D_440,A_439,C_438] :
      ( m1_subset_1(k1_partfun1(A_439,B_436,C_438,D_440,E_435,F_437),k1_zfmisc_1(k2_zfmisc_1(A_439,D_440)))
      | ~ m1_subset_1(F_437,k1_zfmisc_1(k2_zfmisc_1(C_438,D_440)))
      | ~ v1_funct_1(F_437)
      | ~ m1_subset_1(E_435,k1_zfmisc_1(k2_zfmisc_1(A_439,B_436)))
      | ~ v1_funct_1(E_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2342,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2294,c_2312])).

tff(c_2357,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_2342])).

tff(c_2359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2301,c_2357])).

tff(c_2360,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2095])).

tff(c_2761,plain,(
    ! [A_496,B_497,C_498,D_499] :
      ( k2_relset_1(A_496,B_497,C_498) = B_497
      | ~ r2_relset_1(B_497,B_497,k1_partfun1(B_497,A_496,A_496,B_497,D_499,C_498),k6_partfun1(B_497))
      | ~ m1_subset_1(D_499,k1_zfmisc_1(k2_zfmisc_1(B_497,A_496)))
      | ~ v1_funct_2(D_499,B_497,A_496)
      | ~ v1_funct_1(D_499)
      | ~ m1_subset_1(C_498,k1_zfmisc_1(k2_zfmisc_1(A_496,B_497)))
      | ~ v1_funct_2(C_498,A_496,B_497)
      | ~ v1_funct_1(C_498) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2767,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2360,c_2761])).

tff(c_2771,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_66,c_64,c_62,c_1968,c_1984,c_2767])).

tff(c_38,plain,(
    ! [B_31] :
      ( v2_funct_2(B_31,k2_relat_1(B_31))
      | ~ v5_relat_1(B_31,k2_relat_1(B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2782,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2771,c_38])).

tff(c_2790,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1833,c_1880,c_2771,c_2782])).

tff(c_2792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1812,c_2790])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.26/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.26/2.08  
% 5.26/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.26/2.08  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.26/2.08  
% 5.26/2.08  %Foreground sorts:
% 5.26/2.08  
% 5.26/2.08  
% 5.26/2.08  %Background operators:
% 5.26/2.08  
% 5.26/2.08  
% 5.26/2.08  %Foreground operators:
% 5.26/2.08  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.26/2.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.26/2.08  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.26/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.26/2.08  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.26/2.08  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.26/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.26/2.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.26/2.08  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.26/2.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.26/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.26/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.26/2.08  tff('#skF_1', type, '#skF_1': $i).
% 5.26/2.08  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.26/2.08  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.26/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.26/2.08  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.26/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.26/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.26/2.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.26/2.08  tff('#skF_4', type, '#skF_4': $i).
% 5.26/2.08  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.26/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.26/2.08  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.26/2.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.26/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.26/2.08  
% 5.26/2.11  tff(f_171, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 5.26/2.11  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.26/2.11  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.26/2.11  tff(f_134, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.26/2.11  tff(f_48, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.26/2.11  tff(f_132, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.26/2.11  tff(f_102, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.26/2.11  tff(f_100, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.26/2.11  tff(f_122, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.26/2.11  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 5.26/2.11  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.26/2.11  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.26/2.11  tff(f_78, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 5.26/2.11  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 5.26/2.11  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_1)).
% 5.26/2.11  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.26/2.11  tff(f_151, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 5.26/2.11  tff(f_110, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.26/2.11  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.26/2.11  tff(c_110, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.26/2.11  tff(c_122, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_110])).
% 5.26/2.11  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.26/2.11  tff(c_121, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_110])).
% 5.26/2.11  tff(c_143, plain, (![C_69, A_70, B_71]: (v4_relat_1(C_69, A_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.26/2.11  tff(c_156, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_143])).
% 5.26/2.11  tff(c_48, plain, (![A_44]: (k6_relat_1(A_44)=k6_partfun1(A_44))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.26/2.11  tff(c_14, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.26/2.11  tff(c_70, plain, (![A_8]: (k1_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_14])).
% 5.26/2.11  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.26/2.11  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.26/2.11  tff(c_1465, plain, (![A_285, C_289, B_286, D_290, E_287, F_288]: (k1_partfun1(A_285, B_286, C_289, D_290, E_287, F_288)=k5_relat_1(E_287, F_288) | ~m1_subset_1(F_288, k1_zfmisc_1(k2_zfmisc_1(C_289, D_290))) | ~v1_funct_1(F_288) | ~m1_subset_1(E_287, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))) | ~v1_funct_1(E_287))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.26/2.11  tff(c_1469, plain, (![A_285, B_286, E_287]: (k1_partfun1(A_285, B_286, '#skF_2', '#skF_1', E_287, '#skF_4')=k5_relat_1(E_287, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_287, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))) | ~v1_funct_1(E_287))), inference(resolution, [status(thm)], [c_56, c_1465])).
% 5.26/2.11  tff(c_1479, plain, (![A_291, B_292, E_293]: (k1_partfun1(A_291, B_292, '#skF_2', '#skF_1', E_293, '#skF_4')=k5_relat_1(E_293, '#skF_4') | ~m1_subset_1(E_293, k1_zfmisc_1(k2_zfmisc_1(A_291, B_292))) | ~v1_funct_1(E_293))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1469])).
% 5.26/2.11  tff(c_1488, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1479])).
% 5.26/2.11  tff(c_1495, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1488])).
% 5.26/2.11  tff(c_36, plain, (![A_29]: (m1_subset_1(k6_relat_1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.26/2.11  tff(c_67, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36])).
% 5.26/2.11  tff(c_54, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.26/2.11  tff(c_1350, plain, (![D_254, C_255, A_256, B_257]: (D_254=C_255 | ~r2_relset_1(A_256, B_257, C_255, D_254) | ~m1_subset_1(D_254, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))) | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.26/2.11  tff(c_1358, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_54, c_1350])).
% 5.26/2.11  tff(c_1373, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_1358])).
% 5.26/2.11  tff(c_1384, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1373])).
% 5.26/2.11  tff(c_1502, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_1384])).
% 5.26/2.11  tff(c_1514, plain, (![F_297, B_296, A_299, D_300, E_295, C_298]: (m1_subset_1(k1_partfun1(A_299, B_296, C_298, D_300, E_295, F_297), k1_zfmisc_1(k2_zfmisc_1(A_299, D_300))) | ~m1_subset_1(F_297, k1_zfmisc_1(k2_zfmisc_1(C_298, D_300))) | ~v1_funct_1(F_297) | ~m1_subset_1(E_295, k1_zfmisc_1(k2_zfmisc_1(A_299, B_296))) | ~v1_funct_1(E_295))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.26/2.11  tff(c_1544, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1495, c_1514])).
% 5.26/2.11  tff(c_1559, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_1544])).
% 5.26/2.11  tff(c_1561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1502, c_1559])).
% 5.26/2.11  tff(c_1562, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1373])).
% 5.26/2.11  tff(c_1671, plain, (![B_330, E_331, A_329, C_333, F_332, D_334]: (k1_partfun1(A_329, B_330, C_333, D_334, E_331, F_332)=k5_relat_1(E_331, F_332) | ~m1_subset_1(F_332, k1_zfmisc_1(k2_zfmisc_1(C_333, D_334))) | ~v1_funct_1(F_332) | ~m1_subset_1(E_331, k1_zfmisc_1(k2_zfmisc_1(A_329, B_330))) | ~v1_funct_1(E_331))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.26/2.11  tff(c_1675, plain, (![A_329, B_330, E_331]: (k1_partfun1(A_329, B_330, '#skF_2', '#skF_1', E_331, '#skF_4')=k5_relat_1(E_331, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_331, k1_zfmisc_1(k2_zfmisc_1(A_329, B_330))) | ~v1_funct_1(E_331))), inference(resolution, [status(thm)], [c_56, c_1671])).
% 5.26/2.11  tff(c_1685, plain, (![A_335, B_336, E_337]: (k1_partfun1(A_335, B_336, '#skF_2', '#skF_1', E_337, '#skF_4')=k5_relat_1(E_337, '#skF_4') | ~m1_subset_1(E_337, k1_zfmisc_1(k2_zfmisc_1(A_335, B_336))) | ~v1_funct_1(E_337))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1675])).
% 5.26/2.11  tff(c_1694, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1685])).
% 5.26/2.11  tff(c_1701, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1562, c_1694])).
% 5.26/2.11  tff(c_12, plain, (![A_5, B_7]: (r1_tarski(k1_relat_1(k5_relat_1(A_5, B_7)), k1_relat_1(A_5)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.26/2.11  tff(c_157, plain, (![B_72, A_73]: (r1_tarski(k1_relat_1(B_72), A_73) | ~v4_relat_1(B_72, A_73) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.26/2.11  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.26/2.11  tff(c_1160, plain, (![B_231, A_232]: (k1_relat_1(B_231)=A_232 | ~r1_tarski(A_232, k1_relat_1(B_231)) | ~v4_relat_1(B_231, A_232) | ~v1_relat_1(B_231))), inference(resolution, [status(thm)], [c_157, c_2])).
% 5.26/2.11  tff(c_1180, plain, (![A_5, B_7]: (k1_relat_1(k5_relat_1(A_5, B_7))=k1_relat_1(A_5) | ~v4_relat_1(A_5, k1_relat_1(k5_relat_1(A_5, B_7))) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_12, c_1160])).
% 5.26/2.11  tff(c_1711, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_4'))=k1_relat_1('#skF_3') | ~v4_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1'))) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1701, c_1180])).
% 5.26/2.11  tff(c_1726, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_121, c_156, c_70, c_70, c_1701, c_1711])).
% 5.26/2.11  tff(c_52, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.26/2.11  tff(c_101, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 5.26/2.11  tff(c_22, plain, (![A_15]: (v2_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.26/2.11  tff(c_68, plain, (![A_15]: (v2_funct_1(k6_partfun1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_22])).
% 5.26/2.11  tff(c_1213, plain, (![B_239, A_240]: (r1_tarski(k2_relat_1(B_239), k1_relat_1(A_240)) | k1_relat_1(k5_relat_1(B_239, A_240))!=k1_relat_1(B_239) | ~v1_funct_1(B_239) | ~v1_relat_1(B_239) | ~v1_funct_1(A_240) | ~v1_relat_1(A_240))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.26/2.11  tff(c_20, plain, (![B_14, A_12]: (v2_funct_1(B_14) | ~r1_tarski(k2_relat_1(B_14), k1_relat_1(A_12)) | ~v2_funct_1(k5_relat_1(B_14, A_12)) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.26/2.11  tff(c_1232, plain, (![B_239, A_240]: (v2_funct_1(B_239) | ~v2_funct_1(k5_relat_1(B_239, A_240)) | k1_relat_1(k5_relat_1(B_239, A_240))!=k1_relat_1(B_239) | ~v1_funct_1(B_239) | ~v1_relat_1(B_239) | ~v1_funct_1(A_240) | ~v1_relat_1(A_240))), inference(resolution, [status(thm)], [c_1213, c_20])).
% 5.26/2.11  tff(c_1705, plain, (v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | k1_relat_1(k5_relat_1('#skF_3', '#skF_4'))!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1701, c_1232])).
% 5.26/2.11  tff(c_1721, plain, (v2_funct_1('#skF_3') | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_121, c_60, c_122, c_66, c_70, c_1701, c_68, c_1705])).
% 5.26/2.11  tff(c_1722, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_101, c_1721])).
% 5.26/2.11  tff(c_1811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1726, c_1722])).
% 5.26/2.11  tff(c_1812, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 5.26/2.11  tff(c_1822, plain, (![C_341, A_342, B_343]: (v1_relat_1(C_341) | ~m1_subset_1(C_341, k1_zfmisc_1(k2_zfmisc_1(A_342, B_343))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.26/2.11  tff(c_1833, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_1822])).
% 5.26/2.11  tff(c_1869, plain, (![C_354, B_355, A_356]: (v5_relat_1(C_354, B_355) | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(A_356, B_355))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.26/2.11  tff(c_1880, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_1869])).
% 5.26/2.11  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.26/2.11  tff(c_64, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.26/2.11  tff(c_1961, plain, (![A_370, B_371, D_372]: (r2_relset_1(A_370, B_371, D_372, D_372) | ~m1_subset_1(D_372, k1_zfmisc_1(k2_zfmisc_1(A_370, B_371))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.26/2.11  tff(c_1968, plain, (![A_29]: (r2_relset_1(A_29, A_29, k6_partfun1(A_29), k6_partfun1(A_29)))), inference(resolution, [status(thm)], [c_67, c_1961])).
% 5.26/2.11  tff(c_1972, plain, (![A_374, B_375, C_376]: (k2_relset_1(A_374, B_375, C_376)=k2_relat_1(C_376) | ~m1_subset_1(C_376, k1_zfmisc_1(k2_zfmisc_1(A_374, B_375))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.26/2.11  tff(c_1984, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_1972])).
% 5.26/2.11  tff(c_2263, plain, (![A_424, F_427, B_425, C_428, D_429, E_426]: (k1_partfun1(A_424, B_425, C_428, D_429, E_426, F_427)=k5_relat_1(E_426, F_427) | ~m1_subset_1(F_427, k1_zfmisc_1(k2_zfmisc_1(C_428, D_429))) | ~v1_funct_1(F_427) | ~m1_subset_1(E_426, k1_zfmisc_1(k2_zfmisc_1(A_424, B_425))) | ~v1_funct_1(E_426))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.26/2.11  tff(c_2267, plain, (![A_424, B_425, E_426]: (k1_partfun1(A_424, B_425, '#skF_2', '#skF_1', E_426, '#skF_4')=k5_relat_1(E_426, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_426, k1_zfmisc_1(k2_zfmisc_1(A_424, B_425))) | ~v1_funct_1(E_426))), inference(resolution, [status(thm)], [c_56, c_2263])).
% 5.26/2.11  tff(c_2278, plain, (![A_432, B_433, E_434]: (k1_partfun1(A_432, B_433, '#skF_2', '#skF_1', E_434, '#skF_4')=k5_relat_1(E_434, '#skF_4') | ~m1_subset_1(E_434, k1_zfmisc_1(k2_zfmisc_1(A_432, B_433))) | ~v1_funct_1(E_434))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2267])).
% 5.26/2.11  tff(c_2287, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2278])).
% 5.26/2.11  tff(c_2294, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2287])).
% 5.26/2.11  tff(c_2072, plain, (![D_390, C_391, A_392, B_393]: (D_390=C_391 | ~r2_relset_1(A_392, B_393, C_391, D_390) | ~m1_subset_1(D_390, k1_zfmisc_1(k2_zfmisc_1(A_392, B_393))) | ~m1_subset_1(C_391, k1_zfmisc_1(k2_zfmisc_1(A_392, B_393))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.26/2.11  tff(c_2080, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_54, c_2072])).
% 5.26/2.11  tff(c_2095, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_2080])).
% 5.26/2.11  tff(c_2164, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2095])).
% 5.26/2.11  tff(c_2301, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2294, c_2164])).
% 5.26/2.11  tff(c_2312, plain, (![E_435, F_437, B_436, D_440, A_439, C_438]: (m1_subset_1(k1_partfun1(A_439, B_436, C_438, D_440, E_435, F_437), k1_zfmisc_1(k2_zfmisc_1(A_439, D_440))) | ~m1_subset_1(F_437, k1_zfmisc_1(k2_zfmisc_1(C_438, D_440))) | ~v1_funct_1(F_437) | ~m1_subset_1(E_435, k1_zfmisc_1(k2_zfmisc_1(A_439, B_436))) | ~v1_funct_1(E_435))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.26/2.11  tff(c_2342, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2294, c_2312])).
% 5.26/2.11  tff(c_2357, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_2342])).
% 5.26/2.11  tff(c_2359, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2301, c_2357])).
% 5.26/2.11  tff(c_2360, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2095])).
% 5.26/2.11  tff(c_2761, plain, (![A_496, B_497, C_498, D_499]: (k2_relset_1(A_496, B_497, C_498)=B_497 | ~r2_relset_1(B_497, B_497, k1_partfun1(B_497, A_496, A_496, B_497, D_499, C_498), k6_partfun1(B_497)) | ~m1_subset_1(D_499, k1_zfmisc_1(k2_zfmisc_1(B_497, A_496))) | ~v1_funct_2(D_499, B_497, A_496) | ~v1_funct_1(D_499) | ~m1_subset_1(C_498, k1_zfmisc_1(k2_zfmisc_1(A_496, B_497))) | ~v1_funct_2(C_498, A_496, B_497) | ~v1_funct_1(C_498))), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.26/2.11  tff(c_2767, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2360, c_2761])).
% 5.26/2.11  tff(c_2771, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_66, c_64, c_62, c_1968, c_1984, c_2767])).
% 5.26/2.11  tff(c_38, plain, (![B_31]: (v2_funct_2(B_31, k2_relat_1(B_31)) | ~v5_relat_1(B_31, k2_relat_1(B_31)) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.26/2.11  tff(c_2782, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2771, c_38])).
% 5.26/2.11  tff(c_2790, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1833, c_1880, c_2771, c_2782])).
% 5.26/2.11  tff(c_2792, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1812, c_2790])).
% 5.26/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.26/2.11  
% 5.26/2.11  Inference rules
% 5.26/2.11  ----------------------
% 5.26/2.11  #Ref     : 0
% 5.26/2.11  #Sup     : 557
% 5.26/2.11  #Fact    : 0
% 5.26/2.11  #Define  : 0
% 5.26/2.11  #Split   : 8
% 5.26/2.11  #Chain   : 0
% 5.26/2.11  #Close   : 0
% 5.26/2.11  
% 5.26/2.11  Ordering : KBO
% 5.26/2.11  
% 5.26/2.11  Simplification rules
% 5.26/2.11  ----------------------
% 5.26/2.11  #Subsume      : 41
% 5.26/2.11  #Demod        : 556
% 5.26/2.11  #Tautology    : 144
% 5.26/2.11  #SimpNegUnit  : 5
% 5.26/2.11  #BackRed      : 19
% 5.26/2.11  
% 5.26/2.11  #Partial instantiations: 0
% 5.26/2.11  #Strategies tried      : 1
% 5.26/2.11  
% 5.26/2.11  Timing (in seconds)
% 5.26/2.11  ----------------------
% 5.26/2.11  Preprocessing        : 0.45
% 5.26/2.11  Parsing              : 0.23
% 5.26/2.11  CNF conversion       : 0.03
% 5.26/2.11  Main loop            : 0.80
% 5.26/2.11  Inferencing          : 0.29
% 5.26/2.11  Reduction            : 0.28
% 5.26/2.11  Demodulation         : 0.20
% 5.26/2.11  BG Simplification    : 0.04
% 5.26/2.11  Subsumption          : 0.13
% 5.26/2.11  Abstraction          : 0.04
% 5.26/2.11  MUC search           : 0.00
% 5.26/2.11  Cooper               : 0.00
% 5.26/2.11  Total                : 1.29
% 5.26/2.11  Index Insertion      : 0.00
% 5.26/2.11  Index Deletion       : 0.00
% 5.26/2.11  Index Matching       : 0.00
% 5.26/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
