%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:02 EST 2020

% Result     : Theorem 5.03s
% Output     : CNFRefutation 5.38s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 264 expanded)
%              Number of leaves         :   49 ( 115 expanded)
%              Depth                    :   10
%              Number of atoms          :  241 ( 871 expanded)
%              Number of equality atoms :   43 ( 105 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_195,negated_conjecture,(
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

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_158,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_146,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_108,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_156,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_126,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_80,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_175,axiom,(
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

tff(f_134,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_72,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_112,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_143,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_159,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_143])).

tff(c_244,plain,(
    ! [C_77,B_78,A_79] :
      ( v5_relat_1(C_77,B_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_261,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_244])).

tff(c_86,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_68,plain,(
    ! [A_48] : k6_relat_1(A_48) = k6_partfun1(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_26,plain,(
    ! [A_10] : v2_funct_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_88,plain,(
    ! [A_10] : v2_funct_1(k6_partfun1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_26])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_1589,plain,(
    ! [A_282,E_286,F_281,C_285,D_283,B_284] :
      ( m1_subset_1(k1_partfun1(A_282,B_284,C_285,D_283,E_286,F_281),k1_zfmisc_1(k2_zfmisc_1(A_282,D_283)))
      | ~ m1_subset_1(F_281,k1_zfmisc_1(k2_zfmisc_1(C_285,D_283)))
      | ~ v1_funct_1(F_281)
      | ~ m1_subset_1(E_286,k1_zfmisc_1(k2_zfmisc_1(A_282,B_284)))
      | ~ v1_funct_1(E_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_44,plain,(
    ! [A_30] : m1_subset_1(k6_relat_1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_87,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_44])).

tff(c_74,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_1386,plain,(
    ! [D_245,C_246,A_247,B_248] :
      ( D_245 = C_246
      | ~ r2_relset_1(A_247,B_248,C_246,D_245)
      | ~ m1_subset_1(D_245,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248)))
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1398,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_74,c_1386])).

tff(c_1421,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1398])).

tff(c_1431,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1421])).

tff(c_1602,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1589,c_1431])).

tff(c_1642,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_1602])).

tff(c_1643,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1421])).

tff(c_1754,plain,(
    ! [D_303,E_302,C_307,F_306,B_304,A_305] :
      ( k1_partfun1(A_305,B_304,C_307,D_303,E_302,F_306) = k5_relat_1(E_302,F_306)
      | ~ m1_subset_1(F_306,k1_zfmisc_1(k2_zfmisc_1(C_307,D_303)))
      | ~ v1_funct_1(F_306)
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1(A_305,B_304)))
      | ~ v1_funct_1(E_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1760,plain,(
    ! [A_305,B_304,E_302] :
      ( k1_partfun1(A_305,B_304,'#skF_2','#skF_1',E_302,'#skF_4') = k5_relat_1(E_302,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1(A_305,B_304)))
      | ~ v1_funct_1(E_302) ) ),
    inference(resolution,[status(thm)],[c_76,c_1754])).

tff(c_1891,plain,(
    ! [A_330,B_331,E_332] :
      ( k1_partfun1(A_330,B_331,'#skF_2','#skF_1',E_332,'#skF_4') = k5_relat_1(E_332,'#skF_4')
      | ~ m1_subset_1(E_332,k1_zfmisc_1(k2_zfmisc_1(A_330,B_331)))
      | ~ v1_funct_1(E_332) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1760])).

tff(c_1900,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_1891])).

tff(c_1914,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1643,c_1900])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_160,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_143])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_1125,plain,(
    ! [A_211,B_212,C_213] :
      ( k1_relset_1(A_211,B_212,C_213) = k1_relat_1(C_213)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1143,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_1125])).

tff(c_1345,plain,(
    ! [B_242,A_243,C_244] :
      ( k1_xboole_0 = B_242
      | k1_relset_1(A_243,B_242,C_244) = A_243
      | ~ v1_funct_2(C_244,A_243,B_242)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_243,B_242))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1354,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_1345])).

tff(c_1368,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1143,c_1354])).

tff(c_1376,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1368])).

tff(c_1652,plain,(
    ! [B_287,A_288] :
      ( v2_funct_1(B_287)
      | ~ r1_tarski(k2_relat_1(B_287),k1_relat_1(A_288))
      | ~ v2_funct_1(k5_relat_1(B_287,A_288))
      | ~ v1_funct_1(B_287)
      | ~ v1_relat_1(B_287)
      | ~ v1_funct_1(A_288)
      | ~ v1_relat_1(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1655,plain,(
    ! [B_287] :
      ( v2_funct_1(B_287)
      | ~ r1_tarski(k2_relat_1(B_287),'#skF_2')
      | ~ v2_funct_1(k5_relat_1(B_287,'#skF_4'))
      | ~ v1_funct_1(B_287)
      | ~ v1_relat_1(B_287)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1376,c_1652])).

tff(c_1673,plain,(
    ! [B_289] :
      ( v2_funct_1(B_289)
      | ~ r1_tarski(k2_relat_1(B_289),'#skF_2')
      | ~ v2_funct_1(k5_relat_1(B_289,'#skF_4'))
      | ~ v1_funct_1(B_289)
      | ~ v1_relat_1(B_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_80,c_1655])).

tff(c_1683,plain,(
    ! [B_7] :
      ( v2_funct_1(B_7)
      | ~ v2_funct_1(k5_relat_1(B_7,'#skF_4'))
      | ~ v1_funct_1(B_7)
      | ~ v5_relat_1(B_7,'#skF_2')
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_14,c_1673])).

tff(c_1921,plain,
    ( v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1914,c_1683])).

tff(c_1925,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_261,c_86,c_88,c_1921])).

tff(c_1927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_1925])).

tff(c_1928,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1368])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1964,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1928,c_2])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1962,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1928,c_1928,c_8])).

tff(c_178,plain,(
    ! [A_68] :
      ( v2_funct_1(A_68)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68)
      | ~ v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_181,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_178,c_112])).

tff(c_184,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_86,c_181])).

tff(c_185,plain,(
    ! [B_69,A_70] :
      ( v1_xboole_0(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70))
      | ~ v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_194,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_82,c_185])).

tff(c_204,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_194])).

tff(c_1999,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1962,c_204])).

tff(c_2003,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1964,c_1999])).

tff(c_2004,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_2036,plain,(
    ! [C_338,A_339,B_340] :
      ( v1_relat_1(C_338)
      | ~ m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(A_339,B_340))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2053,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_2036])).

tff(c_2136,plain,(
    ! [C_357,B_358,A_359] :
      ( v5_relat_1(C_357,B_358)
      | ~ m1_subset_1(C_357,k1_zfmisc_1(k2_zfmisc_1(A_359,B_358))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2154,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_2136])).

tff(c_84,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_2326,plain,(
    ! [A_394,B_395,C_396] :
      ( k2_relset_1(A_394,B_395,C_396) = k2_relat_1(C_396)
      | ~ m1_subset_1(C_396,k1_zfmisc_1(k2_zfmisc_1(A_394,B_395))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2344,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_2326])).

tff(c_2892,plain,(
    ! [A_469,B_470,C_471,D_472] :
      ( k2_relset_1(A_469,B_470,C_471) = B_470
      | ~ r2_relset_1(B_470,B_470,k1_partfun1(B_470,A_469,A_469,B_470,D_472,C_471),k6_partfun1(B_470))
      | ~ m1_subset_1(D_472,k1_zfmisc_1(k2_zfmisc_1(B_470,A_469)))
      | ~ v1_funct_2(D_472,B_470,A_469)
      | ~ v1_funct_1(D_472)
      | ~ m1_subset_1(C_471,k1_zfmisc_1(k2_zfmisc_1(A_469,B_470)))
      | ~ v1_funct_2(C_471,A_469,B_470)
      | ~ v1_funct_1(C_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_2898,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_2892])).

tff(c_2903,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_86,c_84,c_82,c_2344,c_2898])).

tff(c_58,plain,(
    ! [B_35] :
      ( v2_funct_2(B_35,k2_relat_1(B_35))
      | ~ v5_relat_1(B_35,k2_relat_1(B_35))
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2917,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2903,c_58])).

tff(c_2933,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2053,c_2154,c_2903,c_2917])).

tff(c_2935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2004,c_2933])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:38:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.03/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.38/1.92  
% 5.38/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.38/1.92  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.38/1.92  
% 5.38/1.92  %Foreground sorts:
% 5.38/1.92  
% 5.38/1.92  
% 5.38/1.92  %Background operators:
% 5.38/1.92  
% 5.38/1.92  
% 5.38/1.92  %Foreground operators:
% 5.38/1.92  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.38/1.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.38/1.92  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.38/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.38/1.92  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.38/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.38/1.92  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.38/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.38/1.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.38/1.92  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.38/1.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.38/1.92  tff('#skF_2', type, '#skF_2': $i).
% 5.38/1.92  tff('#skF_3', type, '#skF_3': $i).
% 5.38/1.92  tff('#skF_1', type, '#skF_1': $i).
% 5.38/1.92  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.38/1.92  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.38/1.92  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.38/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.38/1.92  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.38/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.38/1.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.38/1.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.38/1.92  tff('#skF_4', type, '#skF_4': $i).
% 5.38/1.92  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.38/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.38/1.92  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.38/1.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.38/1.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.38/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.38/1.92  
% 5.38/1.94  tff(f_195, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 5.38/1.94  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.38/1.94  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.38/1.94  tff(f_158, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.38/1.94  tff(f_65, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.38/1.94  tff(f_146, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.38/1.94  tff(f_108, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.38/1.94  tff(f_106, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.38/1.94  tff(f_156, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.38/1.94  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.38/1.94  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.38/1.94  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.38/1.94  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_1)).
% 5.38/1.94  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.38/1.94  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.38/1.94  tff(f_61, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_1)).
% 5.38/1.94  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.38/1.94  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.38/1.94  tff(f_175, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 5.38/1.94  tff(f_134, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.38/1.94  tff(c_72, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 5.38/1.94  tff(c_112, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_72])).
% 5.38/1.94  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 5.38/1.94  tff(c_143, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.38/1.94  tff(c_159, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_143])).
% 5.38/1.94  tff(c_244, plain, (![C_77, B_78, A_79]: (v5_relat_1(C_77, B_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.38/1.94  tff(c_261, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_82, c_244])).
% 5.38/1.94  tff(c_86, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 5.38/1.94  tff(c_68, plain, (![A_48]: (k6_relat_1(A_48)=k6_partfun1(A_48))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.38/1.94  tff(c_26, plain, (![A_10]: (v2_funct_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.38/1.94  tff(c_88, plain, (![A_10]: (v2_funct_1(k6_partfun1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_26])).
% 5.38/1.94  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_195])).
% 5.38/1.94  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 5.38/1.94  tff(c_1589, plain, (![A_282, E_286, F_281, C_285, D_283, B_284]: (m1_subset_1(k1_partfun1(A_282, B_284, C_285, D_283, E_286, F_281), k1_zfmisc_1(k2_zfmisc_1(A_282, D_283))) | ~m1_subset_1(F_281, k1_zfmisc_1(k2_zfmisc_1(C_285, D_283))) | ~v1_funct_1(F_281) | ~m1_subset_1(E_286, k1_zfmisc_1(k2_zfmisc_1(A_282, B_284))) | ~v1_funct_1(E_286))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.38/1.94  tff(c_44, plain, (![A_30]: (m1_subset_1(k6_relat_1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.38/1.94  tff(c_87, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_44])).
% 5.38/1.94  tff(c_74, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 5.38/1.94  tff(c_1386, plain, (![D_245, C_246, A_247, B_248]: (D_245=C_246 | ~r2_relset_1(A_247, B_248, C_246, D_245) | ~m1_subset_1(D_245, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.38/1.94  tff(c_1398, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_74, c_1386])).
% 5.38/1.94  tff(c_1421, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_1398])).
% 5.38/1.94  tff(c_1431, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1421])).
% 5.38/1.94  tff(c_1602, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1589, c_1431])).
% 5.38/1.94  tff(c_1642, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_1602])).
% 5.38/1.94  tff(c_1643, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1421])).
% 5.38/1.94  tff(c_1754, plain, (![D_303, E_302, C_307, F_306, B_304, A_305]: (k1_partfun1(A_305, B_304, C_307, D_303, E_302, F_306)=k5_relat_1(E_302, F_306) | ~m1_subset_1(F_306, k1_zfmisc_1(k2_zfmisc_1(C_307, D_303))) | ~v1_funct_1(F_306) | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(A_305, B_304))) | ~v1_funct_1(E_302))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.38/1.94  tff(c_1760, plain, (![A_305, B_304, E_302]: (k1_partfun1(A_305, B_304, '#skF_2', '#skF_1', E_302, '#skF_4')=k5_relat_1(E_302, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(A_305, B_304))) | ~v1_funct_1(E_302))), inference(resolution, [status(thm)], [c_76, c_1754])).
% 5.38/1.94  tff(c_1891, plain, (![A_330, B_331, E_332]: (k1_partfun1(A_330, B_331, '#skF_2', '#skF_1', E_332, '#skF_4')=k5_relat_1(E_332, '#skF_4') | ~m1_subset_1(E_332, k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))) | ~v1_funct_1(E_332))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1760])).
% 5.38/1.94  tff(c_1900, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_1891])).
% 5.38/1.94  tff(c_1914, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1643, c_1900])).
% 5.38/1.94  tff(c_14, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.38/1.94  tff(c_160, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_143])).
% 5.38/1.94  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_195])).
% 5.38/1.94  tff(c_1125, plain, (![A_211, B_212, C_213]: (k1_relset_1(A_211, B_212, C_213)=k1_relat_1(C_213) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.38/1.94  tff(c_1143, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_1125])).
% 5.38/1.94  tff(c_1345, plain, (![B_242, A_243, C_244]: (k1_xboole_0=B_242 | k1_relset_1(A_243, B_242, C_244)=A_243 | ~v1_funct_2(C_244, A_243, B_242) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_243, B_242))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.38/1.94  tff(c_1354, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_1345])).
% 5.38/1.94  tff(c_1368, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1143, c_1354])).
% 5.38/1.94  tff(c_1376, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_1368])).
% 5.38/1.94  tff(c_1652, plain, (![B_287, A_288]: (v2_funct_1(B_287) | ~r1_tarski(k2_relat_1(B_287), k1_relat_1(A_288)) | ~v2_funct_1(k5_relat_1(B_287, A_288)) | ~v1_funct_1(B_287) | ~v1_relat_1(B_287) | ~v1_funct_1(A_288) | ~v1_relat_1(A_288))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.38/1.94  tff(c_1655, plain, (![B_287]: (v2_funct_1(B_287) | ~r1_tarski(k2_relat_1(B_287), '#skF_2') | ~v2_funct_1(k5_relat_1(B_287, '#skF_4')) | ~v1_funct_1(B_287) | ~v1_relat_1(B_287) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1376, c_1652])).
% 5.38/1.94  tff(c_1673, plain, (![B_289]: (v2_funct_1(B_289) | ~r1_tarski(k2_relat_1(B_289), '#skF_2') | ~v2_funct_1(k5_relat_1(B_289, '#skF_4')) | ~v1_funct_1(B_289) | ~v1_relat_1(B_289))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_80, c_1655])).
% 5.38/1.94  tff(c_1683, plain, (![B_7]: (v2_funct_1(B_7) | ~v2_funct_1(k5_relat_1(B_7, '#skF_4')) | ~v1_funct_1(B_7) | ~v5_relat_1(B_7, '#skF_2') | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_14, c_1673])).
% 5.38/1.94  tff(c_1921, plain, (v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1914, c_1683])).
% 5.38/1.94  tff(c_1925, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_261, c_86, c_88, c_1921])).
% 5.38/1.94  tff(c_1927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_1925])).
% 5.38/1.94  tff(c_1928, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1368])).
% 5.38/1.94  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.38/1.94  tff(c_1964, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1928, c_2])).
% 5.38/1.94  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.38/1.94  tff(c_1962, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1928, c_1928, c_8])).
% 5.38/1.94  tff(c_178, plain, (![A_68]: (v2_funct_1(A_68) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68) | ~v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.38/1.94  tff(c_181, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_178, c_112])).
% 5.38/1.94  tff(c_184, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_86, c_181])).
% 5.38/1.94  tff(c_185, plain, (![B_69, A_70]: (v1_xboole_0(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | ~v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.38/1.94  tff(c_194, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_82, c_185])).
% 5.38/1.94  tff(c_204, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_184, c_194])).
% 5.38/1.94  tff(c_1999, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1962, c_204])).
% 5.38/1.94  tff(c_2003, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1964, c_1999])).
% 5.38/1.94  tff(c_2004, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_72])).
% 5.38/1.94  tff(c_2036, plain, (![C_338, A_339, B_340]: (v1_relat_1(C_338) | ~m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(A_339, B_340))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.38/1.94  tff(c_2053, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_2036])).
% 5.38/1.94  tff(c_2136, plain, (![C_357, B_358, A_359]: (v5_relat_1(C_357, B_358) | ~m1_subset_1(C_357, k1_zfmisc_1(k2_zfmisc_1(A_359, B_358))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.38/1.94  tff(c_2154, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_2136])).
% 5.38/1.94  tff(c_84, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 5.38/1.94  tff(c_2326, plain, (![A_394, B_395, C_396]: (k2_relset_1(A_394, B_395, C_396)=k2_relat_1(C_396) | ~m1_subset_1(C_396, k1_zfmisc_1(k2_zfmisc_1(A_394, B_395))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.38/1.94  tff(c_2344, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_2326])).
% 5.38/1.94  tff(c_2892, plain, (![A_469, B_470, C_471, D_472]: (k2_relset_1(A_469, B_470, C_471)=B_470 | ~r2_relset_1(B_470, B_470, k1_partfun1(B_470, A_469, A_469, B_470, D_472, C_471), k6_partfun1(B_470)) | ~m1_subset_1(D_472, k1_zfmisc_1(k2_zfmisc_1(B_470, A_469))) | ~v1_funct_2(D_472, B_470, A_469) | ~v1_funct_1(D_472) | ~m1_subset_1(C_471, k1_zfmisc_1(k2_zfmisc_1(A_469, B_470))) | ~v1_funct_2(C_471, A_469, B_470) | ~v1_funct_1(C_471))), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.38/1.94  tff(c_2898, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_2892])).
% 5.38/1.94  tff(c_2903, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_86, c_84, c_82, c_2344, c_2898])).
% 5.38/1.94  tff(c_58, plain, (![B_35]: (v2_funct_2(B_35, k2_relat_1(B_35)) | ~v5_relat_1(B_35, k2_relat_1(B_35)) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.38/1.94  tff(c_2917, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2903, c_58])).
% 5.38/1.94  tff(c_2933, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2053, c_2154, c_2903, c_2917])).
% 5.38/1.94  tff(c_2935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2004, c_2933])).
% 5.38/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.38/1.94  
% 5.38/1.94  Inference rules
% 5.38/1.94  ----------------------
% 5.38/1.94  #Ref     : 0
% 5.38/1.94  #Sup     : 635
% 5.38/1.94  #Fact    : 0
% 5.38/1.94  #Define  : 0
% 5.38/1.94  #Split   : 27
% 5.38/1.94  #Chain   : 0
% 5.38/1.94  #Close   : 0
% 5.38/1.94  
% 5.38/1.94  Ordering : KBO
% 5.38/1.94  
% 5.38/1.94  Simplification rules
% 5.38/1.94  ----------------------
% 5.38/1.94  #Subsume      : 22
% 5.38/1.94  #Demod        : 399
% 5.38/1.94  #Tautology    : 217
% 5.38/1.94  #SimpNegUnit  : 6
% 5.38/1.94  #BackRed      : 50
% 5.38/1.94  
% 5.38/1.94  #Partial instantiations: 0
% 5.38/1.94  #Strategies tried      : 1
% 5.38/1.94  
% 5.38/1.94  Timing (in seconds)
% 5.38/1.94  ----------------------
% 5.38/1.94  Preprocessing        : 0.37
% 5.38/1.94  Parsing              : 0.20
% 5.38/1.94  CNF conversion       : 0.03
% 5.38/1.94  Main loop            : 0.86
% 5.38/1.94  Inferencing          : 0.30
% 5.38/1.94  Reduction            : 0.31
% 5.38/1.94  Demodulation         : 0.22
% 5.38/1.94  BG Simplification    : 0.04
% 5.38/1.94  Subsumption          : 0.14
% 5.38/1.94  Abstraction          : 0.04
% 5.38/1.94  MUC search           : 0.00
% 5.38/1.94  Cooper               : 0.00
% 5.38/1.94  Total                : 1.28
% 5.38/1.94  Index Insertion      : 0.00
% 5.38/1.94  Index Deletion       : 0.00
% 5.38/1.94  Index Matching       : 0.00
% 5.38/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
