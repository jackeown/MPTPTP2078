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
% DateTime   : Thu Dec  3 10:12:11 EST 2020

% Result     : Theorem 5.06s
% Output     : CNFRefutation 5.06s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 348 expanded)
%              Number of leaves         :   44 ( 144 expanded)
%              Depth                    :    9
%              Number of atoms          :  241 (1068 expanded)
%              Number of equality atoms :   39 ( 129 expanded)
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

tff(f_173,negated_conjecture,(
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

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_136,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_48,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_124,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_104,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_134,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_153,axiom,(
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

tff(f_112,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_54,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_105,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_114,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_127,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_114])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_126,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_114])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_186,plain,(
    ! [C_75,A_76,B_77] :
      ( v4_relat_1(C_75,A_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_198,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_186])).

tff(c_50,plain,(
    ! [A_44] : k6_relat_1(A_44) = k6_partfun1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_14,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_73,plain,(
    ! [A_8] : k1_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_14])).

tff(c_1555,plain,(
    ! [E_297,C_300,B_298,D_302,A_301,F_299] :
      ( m1_subset_1(k1_partfun1(A_301,B_298,C_300,D_302,E_297,F_299),k1_zfmisc_1(k2_zfmisc_1(A_301,D_302)))
      | ~ m1_subset_1(F_299,k1_zfmisc_1(k2_zfmisc_1(C_300,D_302)))
      | ~ v1_funct_1(F_299)
      | ~ m1_subset_1(E_297,k1_zfmisc_1(k2_zfmisc_1(A_301,B_298)))
      | ~ v1_funct_1(E_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_38,plain,(
    ! [A_29] : m1_subset_1(k6_relat_1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_69,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_38])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1374,plain,(
    ! [D_254,C_255,A_256,B_257] :
      ( D_254 = C_255
      | ~ r2_relset_1(A_256,B_257,C_255,D_254)
      | ~ m1_subset_1(D_254,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257)))
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1382,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_1374])).

tff(c_1397,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_1382])).

tff(c_1426,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1397])).

tff(c_1571,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1555,c_1426])).

tff(c_1600,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_62,c_58,c_1571])).

tff(c_1601,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1397])).

tff(c_1696,plain,(
    ! [A_326,E_328,B_327,C_330,F_329,D_331] :
      ( k1_partfun1(A_326,B_327,C_330,D_331,E_328,F_329) = k5_relat_1(E_328,F_329)
      | ~ m1_subset_1(F_329,k1_zfmisc_1(k2_zfmisc_1(C_330,D_331)))
      | ~ v1_funct_1(F_329)
      | ~ m1_subset_1(E_328,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327)))
      | ~ v1_funct_1(E_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1702,plain,(
    ! [A_326,B_327,E_328] :
      ( k1_partfun1(A_326,B_327,'#skF_2','#skF_1',E_328,'#skF_4') = k5_relat_1(E_328,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_328,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327)))
      | ~ v1_funct_1(E_328) ) ),
    inference(resolution,[status(thm)],[c_58,c_1696])).

tff(c_1856,plain,(
    ! [A_344,B_345,E_346] :
      ( k1_partfun1(A_344,B_345,'#skF_2','#skF_1',E_346,'#skF_4') = k5_relat_1(E_346,'#skF_4')
      | ~ m1_subset_1(E_346,k1_zfmisc_1(k2_zfmisc_1(A_344,B_345)))
      | ~ v1_funct_1(E_346) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1702])).

tff(c_1868,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1856])).

tff(c_1879,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1601,c_1868])).

tff(c_12,plain,(
    ! [A_5,B_7] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_5,B_7)),k1_relat_1(A_5))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_153,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(k1_relat_1(B_69),A_70)
      | ~ v4_relat_1(B_69,A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1192,plain,(
    ! [B_231,A_232] :
      ( k1_relat_1(B_231) = A_232
      | ~ r1_tarski(A_232,k1_relat_1(B_231))
      | ~ v4_relat_1(B_231,A_232)
      | ~ v1_relat_1(B_231) ) ),
    inference(resolution,[status(thm)],[c_153,c_2])).

tff(c_1212,plain,(
    ! [A_5,B_7] :
      ( k1_relat_1(k5_relat_1(A_5,B_7)) = k1_relat_1(A_5)
      | ~ v4_relat_1(A_5,k1_relat_1(k5_relat_1(A_5,B_7)))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_1192])).

tff(c_1889,plain,
    ( k1_relat_1(k5_relat_1('#skF_3','#skF_4')) = k1_relat_1('#skF_3')
    | ~ v4_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1')))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1879,c_1212])).

tff(c_1901,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_127,c_198,c_73,c_73,c_1879,c_1889])).

tff(c_20,plain,(
    ! [A_9] : v2_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_70,plain,(
    ! [A_9] : v2_funct_1(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_20])).

tff(c_22,plain,(
    ! [B_12,A_10] :
      ( r1_tarski(k2_relat_1(B_12),k1_relat_1(A_10))
      | k1_relat_1(k5_relat_1(B_12,A_10)) != k1_relat_1(B_12)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1613,plain,(
    ! [B_307,A_308] :
      ( v2_funct_1(B_307)
      | ~ r1_tarski(k2_relat_1(B_307),k1_relat_1(A_308))
      | ~ v2_funct_1(k5_relat_1(B_307,A_308))
      | ~ v1_funct_1(B_307)
      | ~ v1_relat_1(B_307)
      | ~ v1_funct_1(A_308)
      | ~ v1_relat_1(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2287,plain,(
    ! [B_360,A_361] :
      ( v2_funct_1(B_360)
      | ~ v2_funct_1(k5_relat_1(B_360,A_361))
      | k1_relat_1(k5_relat_1(B_360,A_361)) != k1_relat_1(B_360)
      | ~ v1_funct_1(B_360)
      | ~ v1_relat_1(B_360)
      | ~ v1_funct_1(A_361)
      | ~ v1_relat_1(A_361) ) ),
    inference(resolution,[status(thm)],[c_22,c_1613])).

tff(c_2290,plain,
    ( v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | k1_relat_1(k5_relat_1('#skF_3','#skF_4')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1879,c_2287])).

tff(c_2292,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_62,c_126,c_68,c_1901,c_73,c_1879,c_70,c_2290])).

tff(c_2294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_2292])).

tff(c_2295,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2298,plain,(
    ! [C_363,A_364,B_365] :
      ( v1_relat_1(C_363)
      | ~ m1_subset_1(C_363,k1_zfmisc_1(k2_zfmisc_1(A_364,B_365))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2311,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_2298])).

tff(c_2333,plain,(
    ! [C_372,B_373,A_374] :
      ( v5_relat_1(C_372,B_373)
      | ~ m1_subset_1(C_372,k1_zfmisc_1(k2_zfmisc_1(A_374,B_373))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2345,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_2333])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_2422,plain,(
    ! [A_389,B_390,D_391] :
      ( r2_relset_1(A_389,B_390,D_391,D_391)
      | ~ m1_subset_1(D_391,k1_zfmisc_1(k2_zfmisc_1(A_389,B_390))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2429,plain,(
    ! [A_29] : r2_relset_1(A_29,A_29,k6_partfun1(A_29),k6_partfun1(A_29)) ),
    inference(resolution,[status(thm)],[c_69,c_2422])).

tff(c_2446,plain,(
    ! [A_395,B_396,C_397] :
      ( k2_relset_1(A_395,B_396,C_397) = k2_relat_1(C_397)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(A_395,B_396))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2459,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_2446])).

tff(c_2825,plain,(
    ! [C_476,F_475,D_478,E_473,B_474,A_477] :
      ( m1_subset_1(k1_partfun1(A_477,B_474,C_476,D_478,E_473,F_475),k1_zfmisc_1(k2_zfmisc_1(A_477,D_478)))
      | ~ m1_subset_1(F_475,k1_zfmisc_1(k2_zfmisc_1(C_476,D_478)))
      | ~ v1_funct_1(F_475)
      | ~ m1_subset_1(E_473,k1_zfmisc_1(k2_zfmisc_1(A_477,B_474)))
      | ~ v1_funct_1(E_473) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2657,plain,(
    ! [D_423,C_424,A_425,B_426] :
      ( D_423 = C_424
      | ~ r2_relset_1(A_425,B_426,C_424,D_423)
      | ~ m1_subset_1(D_423,k1_zfmisc_1(k2_zfmisc_1(A_425,B_426)))
      | ~ m1_subset_1(C_424,k1_zfmisc_1(k2_zfmisc_1(A_425,B_426))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2665,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_2657])).

tff(c_2680,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_2665])).

tff(c_2694,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2680])).

tff(c_2843,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2825,c_2694])).

tff(c_2873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_62,c_58,c_2843])).

tff(c_2874,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2680])).

tff(c_3207,plain,(
    ! [A_513,B_514,C_515,D_516] :
      ( k2_relset_1(A_513,B_514,C_515) = B_514
      | ~ r2_relset_1(B_514,B_514,k1_partfun1(B_514,A_513,A_513,B_514,D_516,C_515),k6_partfun1(B_514))
      | ~ m1_subset_1(D_516,k1_zfmisc_1(k2_zfmisc_1(B_514,A_513)))
      | ~ v1_funct_2(D_516,B_514,A_513)
      | ~ v1_funct_1(D_516)
      | ~ m1_subset_1(C_515,k1_zfmisc_1(k2_zfmisc_1(A_513,B_514)))
      | ~ v1_funct_2(C_515,A_513,B_514)
      | ~ v1_funct_1(C_515) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_3210,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2874,c_3207])).

tff(c_3212,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_68,c_66,c_64,c_2429,c_2459,c_3210])).

tff(c_40,plain,(
    ! [B_31] :
      ( v2_funct_2(B_31,k2_relat_1(B_31))
      | ~ v5_relat_1(B_31,k2_relat_1(B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3223,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3212,c_40])).

tff(c_3231,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2311,c_2345,c_3212,c_3223])).

tff(c_3233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2295,c_3231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:19:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.06/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.06/1.96  
% 5.06/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.06/1.97  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.06/1.97  
% 5.06/1.97  %Foreground sorts:
% 5.06/1.97  
% 5.06/1.97  
% 5.06/1.97  %Background operators:
% 5.06/1.97  
% 5.06/1.97  
% 5.06/1.97  %Foreground operators:
% 5.06/1.97  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.06/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.06/1.97  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.06/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.06/1.97  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.06/1.97  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.06/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.06/1.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.06/1.97  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.06/1.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.06/1.97  tff('#skF_2', type, '#skF_2': $i).
% 5.06/1.97  tff('#skF_3', type, '#skF_3': $i).
% 5.06/1.97  tff('#skF_1', type, '#skF_1': $i).
% 5.06/1.97  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.06/1.97  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.06/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.06/1.97  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.06/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.06/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.06/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.06/1.97  tff('#skF_4', type, '#skF_4': $i).
% 5.06/1.97  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.06/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.06/1.97  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.06/1.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.06/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.06/1.97  
% 5.06/1.99  tff(f_173, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 5.06/1.99  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.06/1.99  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.06/1.99  tff(f_136, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.06/1.99  tff(f_48, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.06/1.99  tff(f_124, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.06/1.99  tff(f_104, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.06/1.99  tff(f_102, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.06/1.99  tff(f_134, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.06/1.99  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 5.06/1.99  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 5.06/1.99  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.06/1.99  tff(f_52, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.06/1.99  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 5.06/1.99  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_1)).
% 5.06/1.99  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.06/1.99  tff(f_153, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 5.06/1.99  tff(f_112, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.06/1.99  tff(c_54, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.06/1.99  tff(c_105, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 5.06/1.99  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.06/1.99  tff(c_114, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.06/1.99  tff(c_127, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_114])).
% 5.06/1.99  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.06/1.99  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.06/1.99  tff(c_126, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_114])).
% 5.06/1.99  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.06/1.99  tff(c_186, plain, (![C_75, A_76, B_77]: (v4_relat_1(C_75, A_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.06/1.99  tff(c_198, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_186])).
% 5.06/1.99  tff(c_50, plain, (![A_44]: (k6_relat_1(A_44)=k6_partfun1(A_44))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.06/1.99  tff(c_14, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.06/1.99  tff(c_73, plain, (![A_8]: (k1_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_14])).
% 5.06/1.99  tff(c_1555, plain, (![E_297, C_300, B_298, D_302, A_301, F_299]: (m1_subset_1(k1_partfun1(A_301, B_298, C_300, D_302, E_297, F_299), k1_zfmisc_1(k2_zfmisc_1(A_301, D_302))) | ~m1_subset_1(F_299, k1_zfmisc_1(k2_zfmisc_1(C_300, D_302))) | ~v1_funct_1(F_299) | ~m1_subset_1(E_297, k1_zfmisc_1(k2_zfmisc_1(A_301, B_298))) | ~v1_funct_1(E_297))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.06/1.99  tff(c_38, plain, (![A_29]: (m1_subset_1(k6_relat_1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.06/1.99  tff(c_69, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_38])).
% 5.06/1.99  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.06/1.99  tff(c_1374, plain, (![D_254, C_255, A_256, B_257]: (D_254=C_255 | ~r2_relset_1(A_256, B_257, C_255, D_254) | ~m1_subset_1(D_254, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))) | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.06/1.99  tff(c_1382, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_1374])).
% 5.06/1.99  tff(c_1397, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_1382])).
% 5.06/1.99  tff(c_1426, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1397])).
% 5.06/1.99  tff(c_1571, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1555, c_1426])).
% 5.06/1.99  tff(c_1600, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_58, c_1571])).
% 5.06/1.99  tff(c_1601, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1397])).
% 5.06/1.99  tff(c_1696, plain, (![A_326, E_328, B_327, C_330, F_329, D_331]: (k1_partfun1(A_326, B_327, C_330, D_331, E_328, F_329)=k5_relat_1(E_328, F_329) | ~m1_subset_1(F_329, k1_zfmisc_1(k2_zfmisc_1(C_330, D_331))) | ~v1_funct_1(F_329) | ~m1_subset_1(E_328, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))) | ~v1_funct_1(E_328))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.06/1.99  tff(c_1702, plain, (![A_326, B_327, E_328]: (k1_partfun1(A_326, B_327, '#skF_2', '#skF_1', E_328, '#skF_4')=k5_relat_1(E_328, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_328, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))) | ~v1_funct_1(E_328))), inference(resolution, [status(thm)], [c_58, c_1696])).
% 5.06/1.99  tff(c_1856, plain, (![A_344, B_345, E_346]: (k1_partfun1(A_344, B_345, '#skF_2', '#skF_1', E_346, '#skF_4')=k5_relat_1(E_346, '#skF_4') | ~m1_subset_1(E_346, k1_zfmisc_1(k2_zfmisc_1(A_344, B_345))) | ~v1_funct_1(E_346))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1702])).
% 5.06/1.99  tff(c_1868, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1856])).
% 5.06/1.99  tff(c_1879, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1601, c_1868])).
% 5.06/1.99  tff(c_12, plain, (![A_5, B_7]: (r1_tarski(k1_relat_1(k5_relat_1(A_5, B_7)), k1_relat_1(A_5)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.06/1.99  tff(c_153, plain, (![B_69, A_70]: (r1_tarski(k1_relat_1(B_69), A_70) | ~v4_relat_1(B_69, A_70) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.06/1.99  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.06/1.99  tff(c_1192, plain, (![B_231, A_232]: (k1_relat_1(B_231)=A_232 | ~r1_tarski(A_232, k1_relat_1(B_231)) | ~v4_relat_1(B_231, A_232) | ~v1_relat_1(B_231))), inference(resolution, [status(thm)], [c_153, c_2])).
% 5.06/1.99  tff(c_1212, plain, (![A_5, B_7]: (k1_relat_1(k5_relat_1(A_5, B_7))=k1_relat_1(A_5) | ~v4_relat_1(A_5, k1_relat_1(k5_relat_1(A_5, B_7))) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_12, c_1192])).
% 5.06/1.99  tff(c_1889, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_4'))=k1_relat_1('#skF_3') | ~v4_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1'))) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1879, c_1212])).
% 5.06/1.99  tff(c_1901, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_126, c_127, c_198, c_73, c_73, c_1879, c_1889])).
% 5.06/1.99  tff(c_20, plain, (![A_9]: (v2_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.06/1.99  tff(c_70, plain, (![A_9]: (v2_funct_1(k6_partfun1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_20])).
% 5.06/1.99  tff(c_22, plain, (![B_12, A_10]: (r1_tarski(k2_relat_1(B_12), k1_relat_1(A_10)) | k1_relat_1(k5_relat_1(B_12, A_10))!=k1_relat_1(B_12) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.06/1.99  tff(c_1613, plain, (![B_307, A_308]: (v2_funct_1(B_307) | ~r1_tarski(k2_relat_1(B_307), k1_relat_1(A_308)) | ~v2_funct_1(k5_relat_1(B_307, A_308)) | ~v1_funct_1(B_307) | ~v1_relat_1(B_307) | ~v1_funct_1(A_308) | ~v1_relat_1(A_308))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.06/1.99  tff(c_2287, plain, (![B_360, A_361]: (v2_funct_1(B_360) | ~v2_funct_1(k5_relat_1(B_360, A_361)) | k1_relat_1(k5_relat_1(B_360, A_361))!=k1_relat_1(B_360) | ~v1_funct_1(B_360) | ~v1_relat_1(B_360) | ~v1_funct_1(A_361) | ~v1_relat_1(A_361))), inference(resolution, [status(thm)], [c_22, c_1613])).
% 5.06/1.99  tff(c_2290, plain, (v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | k1_relat_1(k5_relat_1('#skF_3', '#skF_4'))!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1879, c_2287])).
% 5.06/1.99  tff(c_2292, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_62, c_126, c_68, c_1901, c_73, c_1879, c_70, c_2290])).
% 5.06/1.99  tff(c_2294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_2292])).
% 5.06/1.99  tff(c_2295, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 5.06/1.99  tff(c_2298, plain, (![C_363, A_364, B_365]: (v1_relat_1(C_363) | ~m1_subset_1(C_363, k1_zfmisc_1(k2_zfmisc_1(A_364, B_365))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.06/1.99  tff(c_2311, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_2298])).
% 5.06/1.99  tff(c_2333, plain, (![C_372, B_373, A_374]: (v5_relat_1(C_372, B_373) | ~m1_subset_1(C_372, k1_zfmisc_1(k2_zfmisc_1(A_374, B_373))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.06/1.99  tff(c_2345, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_2333])).
% 5.06/1.99  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.06/1.99  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.06/1.99  tff(c_2422, plain, (![A_389, B_390, D_391]: (r2_relset_1(A_389, B_390, D_391, D_391) | ~m1_subset_1(D_391, k1_zfmisc_1(k2_zfmisc_1(A_389, B_390))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.06/1.99  tff(c_2429, plain, (![A_29]: (r2_relset_1(A_29, A_29, k6_partfun1(A_29), k6_partfun1(A_29)))), inference(resolution, [status(thm)], [c_69, c_2422])).
% 5.06/1.99  tff(c_2446, plain, (![A_395, B_396, C_397]: (k2_relset_1(A_395, B_396, C_397)=k2_relat_1(C_397) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(A_395, B_396))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.06/1.99  tff(c_2459, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_2446])).
% 5.06/1.99  tff(c_2825, plain, (![C_476, F_475, D_478, E_473, B_474, A_477]: (m1_subset_1(k1_partfun1(A_477, B_474, C_476, D_478, E_473, F_475), k1_zfmisc_1(k2_zfmisc_1(A_477, D_478))) | ~m1_subset_1(F_475, k1_zfmisc_1(k2_zfmisc_1(C_476, D_478))) | ~v1_funct_1(F_475) | ~m1_subset_1(E_473, k1_zfmisc_1(k2_zfmisc_1(A_477, B_474))) | ~v1_funct_1(E_473))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.06/1.99  tff(c_2657, plain, (![D_423, C_424, A_425, B_426]: (D_423=C_424 | ~r2_relset_1(A_425, B_426, C_424, D_423) | ~m1_subset_1(D_423, k1_zfmisc_1(k2_zfmisc_1(A_425, B_426))) | ~m1_subset_1(C_424, k1_zfmisc_1(k2_zfmisc_1(A_425, B_426))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.06/1.99  tff(c_2665, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_2657])).
% 5.06/1.99  tff(c_2680, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_2665])).
% 5.06/1.99  tff(c_2694, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2680])).
% 5.06/1.99  tff(c_2843, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2825, c_2694])).
% 5.06/1.99  tff(c_2873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_58, c_2843])).
% 5.06/1.99  tff(c_2874, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2680])).
% 5.06/1.99  tff(c_3207, plain, (![A_513, B_514, C_515, D_516]: (k2_relset_1(A_513, B_514, C_515)=B_514 | ~r2_relset_1(B_514, B_514, k1_partfun1(B_514, A_513, A_513, B_514, D_516, C_515), k6_partfun1(B_514)) | ~m1_subset_1(D_516, k1_zfmisc_1(k2_zfmisc_1(B_514, A_513))) | ~v1_funct_2(D_516, B_514, A_513) | ~v1_funct_1(D_516) | ~m1_subset_1(C_515, k1_zfmisc_1(k2_zfmisc_1(A_513, B_514))) | ~v1_funct_2(C_515, A_513, B_514) | ~v1_funct_1(C_515))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.06/1.99  tff(c_3210, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2874, c_3207])).
% 5.06/1.99  tff(c_3212, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_68, c_66, c_64, c_2429, c_2459, c_3210])).
% 5.06/1.99  tff(c_40, plain, (![B_31]: (v2_funct_2(B_31, k2_relat_1(B_31)) | ~v5_relat_1(B_31, k2_relat_1(B_31)) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.06/1.99  tff(c_3223, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3212, c_40])).
% 5.06/1.99  tff(c_3231, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2311, c_2345, c_3212, c_3223])).
% 5.06/1.99  tff(c_3233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2295, c_3231])).
% 5.06/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.06/1.99  
% 5.06/1.99  Inference rules
% 5.06/1.99  ----------------------
% 5.06/1.99  #Ref     : 0
% 5.06/1.99  #Sup     : 648
% 5.06/1.99  #Fact    : 0
% 5.06/1.99  #Define  : 0
% 5.06/1.99  #Split   : 10
% 5.06/1.99  #Chain   : 0
% 5.06/1.99  #Close   : 0
% 5.06/1.99  
% 5.06/1.99  Ordering : KBO
% 5.06/1.99  
% 5.06/1.99  Simplification rules
% 5.06/1.99  ----------------------
% 5.06/1.99  #Subsume      : 40
% 5.06/1.99  #Demod        : 646
% 5.06/1.99  #Tautology    : 171
% 5.06/1.99  #SimpNegUnit  : 4
% 5.06/1.99  #BackRed      : 18
% 5.06/1.99  
% 5.06/1.99  #Partial instantiations: 0
% 5.06/1.99  #Strategies tried      : 1
% 5.06/1.99  
% 5.06/1.99  Timing (in seconds)
% 5.06/1.99  ----------------------
% 5.42/1.99  Preprocessing        : 0.37
% 5.42/1.99  Parsing              : 0.21
% 5.42/1.99  CNF conversion       : 0.02
% 5.42/1.99  Main loop            : 0.82
% 5.42/1.99  Inferencing          : 0.30
% 5.42/1.99  Reduction            : 0.28
% 5.42/1.99  Demodulation         : 0.21
% 5.42/1.99  BG Simplification    : 0.03
% 5.42/1.99  Subsumption          : 0.13
% 5.42/1.99  Abstraction          : 0.04
% 5.42/1.99  MUC search           : 0.00
% 5.42/1.99  Cooper               : 0.00
% 5.42/1.99  Total                : 1.22
% 5.42/1.99  Index Insertion      : 0.00
% 5.42/1.99  Index Deletion       : 0.00
% 5.42/1.99  Index Matching       : 0.00
% 5.42/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
