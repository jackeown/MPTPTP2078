%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:19 EST 2020

% Result     : Theorem 6.71s
% Output     : CNFRefutation 6.80s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 820 expanded)
%              Number of leaves         :   49 ( 294 expanded)
%              Depth                    :   15
%              Number of atoms          :  396 (2293 expanded)
%              Number of equality atoms :   81 ( 257 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_178,negated_conjecture,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_136,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_88,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_134,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_124,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_104,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_158,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_75,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_86,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_39,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_66,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_148,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_78,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_60,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_38,plain,(
    ! [A_24] : v2_funct_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_82,plain,(
    ! [A_24] : v2_funct_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_38])).

tff(c_1886,plain,(
    ! [A_263,E_262,B_267,D_265,C_264,F_266] :
      ( k1_partfun1(A_263,B_267,C_264,D_265,E_262,F_266) = k5_relat_1(E_262,F_266)
      | ~ m1_subset_1(F_266,k1_zfmisc_1(k2_zfmisc_1(C_264,D_265)))
      | ~ v1_funct_1(F_266)
      | ~ m1_subset_1(E_262,k1_zfmisc_1(k2_zfmisc_1(A_263,B_267)))
      | ~ v1_funct_1(E_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1892,plain,(
    ! [A_263,B_267,E_262] :
      ( k1_partfun1(A_263,B_267,'#skF_2','#skF_1',E_262,'#skF_4') = k5_relat_1(E_262,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_262,k1_zfmisc_1(k2_zfmisc_1(A_263,B_267)))
      | ~ v1_funct_1(E_262) ) ),
    inference(resolution,[status(thm)],[c_70,c_1886])).

tff(c_2161,plain,(
    ! [A_297,B_298,E_299] :
      ( k1_partfun1(A_297,B_298,'#skF_2','#skF_1',E_299,'#skF_4') = k5_relat_1(E_299,'#skF_4')
      | ~ m1_subset_1(E_299,k1_zfmisc_1(k2_zfmisc_1(A_297,B_298)))
      | ~ v1_funct_1(E_299) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1892])).

tff(c_2173,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_2161])).

tff(c_2190,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2173])).

tff(c_54,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39] :
      ( m1_subset_1(k1_partfun1(A_35,B_36,C_37,D_38,E_39,F_40),k1_zfmisc_1(k2_zfmisc_1(A_35,D_38)))
      | ~ m1_subset_1(F_40,k1_zfmisc_1(k2_zfmisc_1(C_37,D_38)))
      | ~ v1_funct_1(F_40)
      | ~ m1_subset_1(E_39,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_1(E_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2427,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2190,c_54])).

tff(c_2434,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_2427])).

tff(c_48,plain,(
    ! [A_32] : m1_subset_1(k6_relat_1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_81,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_48])).

tff(c_68,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1686,plain,(
    ! [D_242,C_243,A_244,B_245] :
      ( D_242 = C_243
      | ~ r2_relset_1(A_244,B_245,C_243,D_242)
      | ~ m1_subset_1(D_242,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245)))
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1696,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_1686])).

tff(c_1715,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1696])).

tff(c_1718,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1715])).

tff(c_2498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2434,c_2190,c_1718])).

tff(c_2499,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1715])).

tff(c_3158,plain,(
    ! [C_375,D_372,A_374,E_371,B_373] :
      ( k1_xboole_0 = C_375
      | v2_funct_1(D_372)
      | ~ v2_funct_1(k1_partfun1(A_374,B_373,B_373,C_375,D_372,E_371))
      | ~ m1_subset_1(E_371,k1_zfmisc_1(k2_zfmisc_1(B_373,C_375)))
      | ~ v1_funct_2(E_371,B_373,C_375)
      | ~ v1_funct_1(E_371)
      | ~ m1_subset_1(D_372,k1_zfmisc_1(k2_zfmisc_1(A_374,B_373)))
      | ~ v1_funct_2(D_372,A_374,B_373)
      | ~ v1_funct_1(D_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3160,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2499,c_3158])).

tff(c_3162,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_82,c_3160])).

tff(c_3163,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_3162])).

tff(c_30,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_175,plain,(
    ! [B_71,A_72] :
      ( v1_relat_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_187,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_175])).

tff(c_199,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_187])).

tff(c_296,plain,(
    ! [C_80,B_81,A_82] :
      ( v5_relat_1(C_80,B_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_314,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_296])).

tff(c_606,plain,(
    ! [B_117,A_118] :
      ( k2_relat_1(B_117) = A_118
      | ~ v2_funct_2(B_117,A_118)
      | ~ v5_relat_1(B_117,A_118)
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_621,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_314,c_606])).

tff(c_638,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_621])).

tff(c_656,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_638])).

tff(c_184,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_175])).

tff(c_196,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_184])).

tff(c_36,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_83,plain,(
    ! [A_23] : k2_relat_1(k6_partfun1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_36])).

tff(c_1031,plain,(
    ! [C_171,D_173,F_170,B_174,A_169,E_172] :
      ( m1_subset_1(k1_partfun1(A_169,B_174,C_171,D_173,E_172,F_170),k1_zfmisc_1(k2_zfmisc_1(A_169,D_173)))
      | ~ m1_subset_1(F_170,k1_zfmisc_1(k2_zfmisc_1(C_171,D_173)))
      | ~ v1_funct_1(F_170)
      | ~ m1_subset_1(E_172,k1_zfmisc_1(k2_zfmisc_1(A_169,B_174)))
      | ~ v1_funct_1(E_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_716,plain,(
    ! [D_122,C_123,A_124,B_125] :
      ( D_122 = C_123
      | ~ r2_relset_1(A_124,B_125,C_123,D_122)
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_726,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_716])).

tff(c_745,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_726])).

tff(c_767,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_745])).

tff(c_1039,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1031,c_767])).

tff(c_1070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_1039])).

tff(c_1071,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_745])).

tff(c_1264,plain,(
    ! [B_205,E_200,D_203,C_202,F_204,A_201] :
      ( k1_partfun1(A_201,B_205,C_202,D_203,E_200,F_204) = k5_relat_1(E_200,F_204)
      | ~ m1_subset_1(F_204,k1_zfmisc_1(k2_zfmisc_1(C_202,D_203)))
      | ~ v1_funct_1(F_204)
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_201,B_205)))
      | ~ v1_funct_1(E_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1270,plain,(
    ! [A_201,B_205,E_200] :
      ( k1_partfun1(A_201,B_205,'#skF_2','#skF_1',E_200,'#skF_4') = k5_relat_1(E_200,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_201,B_205)))
      | ~ v1_funct_1(E_200) ) ),
    inference(resolution,[status(thm)],[c_70,c_1264])).

tff(c_1559,plain,(
    ! [A_239,B_240,E_241] :
      ( k1_partfun1(A_239,B_240,'#skF_2','#skF_1',E_241,'#skF_4') = k5_relat_1(E_241,'#skF_4')
      | ~ m1_subset_1(E_241,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240)))
      | ~ v1_funct_1(E_241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1270])).

tff(c_1571,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_1559])).

tff(c_1588,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1071,c_1571])).

tff(c_32,plain,(
    ! [A_20,B_22] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_20,B_22)),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_401,plain,(
    ! [B_100,A_101] :
      ( r1_tarski(k2_relat_1(B_100),A_101)
      | ~ v5_relat_1(B_100,A_101)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1172,plain,(
    ! [B_192,A_193] :
      ( k2_relat_1(B_192) = A_193
      | ~ r1_tarski(A_193,k2_relat_1(B_192))
      | ~ v5_relat_1(B_192,A_193)
      | ~ v1_relat_1(B_192) ) ),
    inference(resolution,[status(thm)],[c_401,c_4])).

tff(c_1202,plain,(
    ! [A_20,B_22] :
      ( k2_relat_1(k5_relat_1(A_20,B_22)) = k2_relat_1(B_22)
      | ~ v5_relat_1(B_22,k2_relat_1(k5_relat_1(A_20,B_22)))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_20) ) ),
    inference(resolution,[status(thm)],[c_32,c_1172])).

tff(c_1595,plain,
    ( k2_relat_1(k5_relat_1('#skF_3','#skF_4')) = k2_relat_1('#skF_4')
    | ~ v5_relat_1('#skF_4',k2_relat_1(k6_partfun1('#skF_1')))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1588,c_1202])).

tff(c_1605,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_199,c_314,c_83,c_83,c_1588,c_1595])).

tff(c_362,plain,(
    ! [B_92,A_93] :
      ( v5_relat_1(B_92,A_93)
      | ~ r1_tarski(k2_relat_1(B_92),A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_377,plain,(
    ! [B_92] :
      ( v5_relat_1(B_92,k2_relat_1(B_92))
      | ~ v1_relat_1(B_92) ) ),
    inference(resolution,[status(thm)],[c_8,c_362])).

tff(c_464,plain,(
    ! [B_105] :
      ( v2_funct_2(B_105,k2_relat_1(B_105))
      | ~ v5_relat_1(B_105,k2_relat_1(B_105))
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_485,plain,(
    ! [B_92] :
      ( v2_funct_2(B_92,k2_relat_1(B_92))
      | ~ v1_relat_1(B_92) ) ),
    inference(resolution,[status(thm)],[c_377,c_464])).

tff(c_1626,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1605,c_485])).

tff(c_1647,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_1626])).

tff(c_1649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_656,c_1647])).

tff(c_1650,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_638])).

tff(c_26,plain,(
    ! [B_17,A_16] :
      ( v5_relat_1(B_17,A_16)
      | ~ r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1670,plain,(
    ! [A_16] :
      ( v5_relat_1('#skF_4',A_16)
      | ~ r1_tarski('#skF_1',A_16)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1650,c_26])).

tff(c_2521,plain,(
    ! [A_311] :
      ( v5_relat_1('#skF_4',A_311)
      | ~ r1_tarski('#skF_1',A_311) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_1670])).

tff(c_12,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_159,plain,(
    ! [B_68,A_69] :
      ( ~ r1_xboole_0(B_68,A_69)
      | ~ r1_tarski(B_68,A_69)
      | v1_xboole_0(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_163,plain,(
    ! [A_5] :
      ( ~ r1_tarski(A_5,k1_xboole_0)
      | v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_159])).

tff(c_424,plain,(
    ! [B_100] :
      ( v1_xboole_0(k2_relat_1(B_100))
      | ~ v5_relat_1(B_100,k1_xboole_0)
      | ~ v1_relat_1(B_100) ) ),
    inference(resolution,[status(thm)],[c_401,c_163])).

tff(c_1655,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v5_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1650,c_424])).

tff(c_1674,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_1655])).

tff(c_1717,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1674])).

tff(c_2536,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2521,c_1717])).

tff(c_3175,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3163,c_2536])).

tff(c_3203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3175])).

tff(c_3204,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1674])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3209,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3204,c_2])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3232,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3209,c_3209,c_18])).

tff(c_229,plain,(
    ! [B_78,A_79] :
      ( v1_xboole_0(B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_79))
      | ~ v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_247,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_229])).

tff(c_319,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_3390,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3232,c_319])).

tff(c_3394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3204,c_3390])).

tff(c_3395,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_3400,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3395,c_2])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3413,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3400,c_3400,c_20])).

tff(c_3416,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3400,c_3400,c_18])).

tff(c_3396,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_3404,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3396,c_2])).

tff(c_3476,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3400,c_3404])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3861,plain,(
    ! [B_438,A_439] :
      ( B_438 = '#skF_4'
      | A_439 = '#skF_4'
      | k2_zfmisc_1(A_439,B_438) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3400,c_3400,c_3400,c_16])).

tff(c_3875,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3476,c_3861])).

tff(c_3876,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3875])).

tff(c_246,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_229])).

tff(c_274,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_3883,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3876,c_274])).

tff(c_3891,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3395,c_3416,c_3883])).

tff(c_3892,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3875])).

tff(c_3899,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3892,c_274])).

tff(c_3907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3395,c_3413,c_3899])).

tff(c_3908,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_3932,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3908,c_2])).

tff(c_164,plain,(
    ! [A_70] :
      ( ~ r1_tarski(A_70,k1_xboole_0)
      | v1_xboole_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_12,c_159])).

tff(c_173,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_164])).

tff(c_149,plain,(
    ! [A_67] : m1_subset_1(k6_partfun1(A_67),k1_zfmisc_1(k2_zfmisc_1(A_67,A_67))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_48])).

tff(c_153,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_149])).

tff(c_232,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_153,c_229])).

tff(c_244,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_232])).

tff(c_251,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_244,c_2])).

tff(c_268,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_82])).

tff(c_3933,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3932,c_268])).

tff(c_3945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_3933])).

tff(c_3946,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_3980,plain,(
    ! [B_447,A_448] :
      ( v1_relat_1(B_447)
      | ~ m1_subset_1(B_447,k1_zfmisc_1(A_448))
      | ~ v1_relat_1(A_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3992,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_3980])).

tff(c_4004,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3992])).

tff(c_4165,plain,(
    ! [C_466,B_467,A_468] :
      ( v5_relat_1(C_466,B_467)
      | ~ m1_subset_1(C_466,k1_zfmisc_1(k2_zfmisc_1(A_468,B_467))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4184,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_4165])).

tff(c_3989,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_3980])).

tff(c_4001,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3989])).

tff(c_4660,plain,(
    ! [F_527,C_525,D_526,E_523,A_524,B_528] :
      ( k1_partfun1(A_524,B_528,C_525,D_526,E_523,F_527) = k5_relat_1(E_523,F_527)
      | ~ m1_subset_1(F_527,k1_zfmisc_1(k2_zfmisc_1(C_525,D_526)))
      | ~ v1_funct_1(F_527)
      | ~ m1_subset_1(E_523,k1_zfmisc_1(k2_zfmisc_1(A_524,B_528)))
      | ~ v1_funct_1(E_523) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_4666,plain,(
    ! [A_524,B_528,E_523] :
      ( k1_partfun1(A_524,B_528,'#skF_2','#skF_1',E_523,'#skF_4') = k5_relat_1(E_523,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_523,k1_zfmisc_1(k2_zfmisc_1(A_524,B_528)))
      | ~ v1_funct_1(E_523) ) ),
    inference(resolution,[status(thm)],[c_70,c_4660])).

tff(c_4834,plain,(
    ! [A_547,B_548,E_549] :
      ( k1_partfun1(A_547,B_548,'#skF_2','#skF_1',E_549,'#skF_4') = k5_relat_1(E_549,'#skF_4')
      | ~ m1_subset_1(E_549,k1_zfmisc_1(k2_zfmisc_1(A_547,B_548)))
      | ~ v1_funct_1(E_549) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4666])).

tff(c_4843,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_4834])).

tff(c_4857,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4843])).

tff(c_4866,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4857,c_54])).

tff(c_4870,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_4866])).

tff(c_4439,plain,(
    ! [D_496,C_497,A_498,B_499] :
      ( D_496 = C_497
      | ~ r2_relset_1(A_498,B_499,C_497,D_496)
      | ~ m1_subset_1(D_496,k1_zfmisc_1(k2_zfmisc_1(A_498,B_499)))
      | ~ m1_subset_1(C_497,k1_zfmisc_1(k2_zfmisc_1(A_498,B_499))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4449,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_4439])).

tff(c_4468,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_4449])).

tff(c_5165,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4870,c_4857,c_4857,c_4468])).

tff(c_5186,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5165,c_32])).

tff(c_5192,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4001,c_4004,c_83,c_5186])).

tff(c_4197,plain,(
    ! [B_473,A_474] :
      ( r1_tarski(k2_relat_1(B_473),A_474)
      | ~ v5_relat_1(B_473,A_474)
      | ~ v1_relat_1(B_473) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4219,plain,(
    ! [B_473,A_474] :
      ( k2_relat_1(B_473) = A_474
      | ~ r1_tarski(A_474,k2_relat_1(B_473))
      | ~ v5_relat_1(B_473,A_474)
      | ~ v1_relat_1(B_473) ) ),
    inference(resolution,[status(thm)],[c_4197,c_4])).

tff(c_5196,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5192,c_4219])).

tff(c_5201,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4004,c_4184,c_5196])).

tff(c_4132,plain,(
    ! [B_461,A_462] :
      ( v5_relat_1(B_461,A_462)
      | ~ r1_tarski(k2_relat_1(B_461),A_462)
      | ~ v1_relat_1(B_461) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4147,plain,(
    ! [B_461] :
      ( v5_relat_1(B_461,k2_relat_1(B_461))
      | ~ v1_relat_1(B_461) ) ),
    inference(resolution,[status(thm)],[c_8,c_4132])).

tff(c_4248,plain,(
    ! [B_479] :
      ( v2_funct_2(B_479,k2_relat_1(B_479))
      | ~ v5_relat_1(B_479,k2_relat_1(B_479))
      | ~ v1_relat_1(B_479) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4262,plain,(
    ! [B_461] :
      ( v2_funct_2(B_461,k2_relat_1(B_461))
      | ~ v1_relat_1(B_461) ) ),
    inference(resolution,[status(thm)],[c_4147,c_4248])).

tff(c_5220,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5201,c_4262])).

tff(c_5241,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4004,c_5220])).

tff(c_5243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3946,c_5241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.71/2.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.80/2.37  
% 6.80/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.80/2.37  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.80/2.37  
% 6.80/2.37  %Foreground sorts:
% 6.80/2.37  
% 6.80/2.37  
% 6.80/2.37  %Background operators:
% 6.80/2.37  
% 6.80/2.37  
% 6.80/2.37  %Foreground operators:
% 6.80/2.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.80/2.37  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.80/2.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.80/2.37  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.80/2.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.80/2.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.80/2.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.80/2.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.80/2.37  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.80/2.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.80/2.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.80/2.37  tff('#skF_2', type, '#skF_2': $i).
% 6.80/2.37  tff('#skF_3', type, '#skF_3': $i).
% 6.80/2.37  tff('#skF_1', type, '#skF_1': $i).
% 6.80/2.37  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.80/2.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.80/2.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.80/2.37  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.80/2.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.80/2.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.80/2.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.80/2.37  tff('#skF_4', type, '#skF_4': $i).
% 6.80/2.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.80/2.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.80/2.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.80/2.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.80/2.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.80/2.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.80/2.37  
% 6.80/2.40  tff(f_178, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 6.80/2.40  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.80/2.40  tff(f_136, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.80/2.40  tff(f_88, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 6.80/2.40  tff(f_134, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.80/2.40  tff(f_124, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.80/2.40  tff(f_104, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 6.80/2.40  tff(f_102, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.80/2.40  tff(f_158, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 6.80/2.40  tff(f_75, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.80/2.40  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.80/2.40  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.80/2.40  tff(f_112, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.80/2.40  tff(f_86, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 6.80/2.40  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 6.80/2.40  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.80/2.40  tff(f_39, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 6.80/2.40  tff(f_47, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 6.80/2.40  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.80/2.40  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.80/2.40  tff(f_60, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 6.80/2.40  tff(c_66, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 6.80/2.40  tff(c_148, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 6.80/2.40  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.80/2.40  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 6.80/2.40  tff(c_78, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 6.80/2.40  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 6.80/2.40  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 6.80/2.40  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 6.80/2.40  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 6.80/2.40  tff(c_60, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.80/2.40  tff(c_38, plain, (![A_24]: (v2_funct_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.80/2.40  tff(c_82, plain, (![A_24]: (v2_funct_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_38])).
% 6.80/2.40  tff(c_1886, plain, (![A_263, E_262, B_267, D_265, C_264, F_266]: (k1_partfun1(A_263, B_267, C_264, D_265, E_262, F_266)=k5_relat_1(E_262, F_266) | ~m1_subset_1(F_266, k1_zfmisc_1(k2_zfmisc_1(C_264, D_265))) | ~v1_funct_1(F_266) | ~m1_subset_1(E_262, k1_zfmisc_1(k2_zfmisc_1(A_263, B_267))) | ~v1_funct_1(E_262))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.80/2.40  tff(c_1892, plain, (![A_263, B_267, E_262]: (k1_partfun1(A_263, B_267, '#skF_2', '#skF_1', E_262, '#skF_4')=k5_relat_1(E_262, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_262, k1_zfmisc_1(k2_zfmisc_1(A_263, B_267))) | ~v1_funct_1(E_262))), inference(resolution, [status(thm)], [c_70, c_1886])).
% 6.80/2.40  tff(c_2161, plain, (![A_297, B_298, E_299]: (k1_partfun1(A_297, B_298, '#skF_2', '#skF_1', E_299, '#skF_4')=k5_relat_1(E_299, '#skF_4') | ~m1_subset_1(E_299, k1_zfmisc_1(k2_zfmisc_1(A_297, B_298))) | ~v1_funct_1(E_299))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1892])).
% 6.80/2.40  tff(c_2173, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_2161])).
% 6.80/2.40  tff(c_2190, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2173])).
% 6.80/2.40  tff(c_54, plain, (![A_35, F_40, B_36, C_37, D_38, E_39]: (m1_subset_1(k1_partfun1(A_35, B_36, C_37, D_38, E_39, F_40), k1_zfmisc_1(k2_zfmisc_1(A_35, D_38))) | ~m1_subset_1(F_40, k1_zfmisc_1(k2_zfmisc_1(C_37, D_38))) | ~v1_funct_1(F_40) | ~m1_subset_1(E_39, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_1(E_39))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.80/2.40  tff(c_2427, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2190, c_54])).
% 6.80/2.40  tff(c_2434, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_2427])).
% 6.80/2.40  tff(c_48, plain, (![A_32]: (m1_subset_1(k6_relat_1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.80/2.40  tff(c_81, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_48])).
% 6.80/2.40  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 6.80/2.40  tff(c_1686, plain, (![D_242, C_243, A_244, B_245]: (D_242=C_243 | ~r2_relset_1(A_244, B_245, C_243, D_242) | ~m1_subset_1(D_242, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.80/2.40  tff(c_1696, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_1686])).
% 6.80/2.40  tff(c_1715, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1696])).
% 6.80/2.40  tff(c_1718, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1715])).
% 6.80/2.40  tff(c_2498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2434, c_2190, c_1718])).
% 6.80/2.40  tff(c_2499, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1715])).
% 6.80/2.40  tff(c_3158, plain, (![C_375, D_372, A_374, E_371, B_373]: (k1_xboole_0=C_375 | v2_funct_1(D_372) | ~v2_funct_1(k1_partfun1(A_374, B_373, B_373, C_375, D_372, E_371)) | ~m1_subset_1(E_371, k1_zfmisc_1(k2_zfmisc_1(B_373, C_375))) | ~v1_funct_2(E_371, B_373, C_375) | ~v1_funct_1(E_371) | ~m1_subset_1(D_372, k1_zfmisc_1(k2_zfmisc_1(A_374, B_373))) | ~v1_funct_2(D_372, A_374, B_373) | ~v1_funct_1(D_372))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.80/2.40  tff(c_3160, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2499, c_3158])).
% 6.80/2.40  tff(c_3162, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_82, c_3160])).
% 6.80/2.40  tff(c_3163, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_148, c_3162])).
% 6.80/2.40  tff(c_30, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.80/2.40  tff(c_175, plain, (![B_71, A_72]: (v1_relat_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.80/2.40  tff(c_187, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_175])).
% 6.80/2.40  tff(c_199, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_187])).
% 6.80/2.40  tff(c_296, plain, (![C_80, B_81, A_82]: (v5_relat_1(C_80, B_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.80/2.40  tff(c_314, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_296])).
% 6.80/2.40  tff(c_606, plain, (![B_117, A_118]: (k2_relat_1(B_117)=A_118 | ~v2_funct_2(B_117, A_118) | ~v5_relat_1(B_117, A_118) | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.80/2.40  tff(c_621, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_314, c_606])).
% 6.80/2.40  tff(c_638, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_621])).
% 6.80/2.40  tff(c_656, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_638])).
% 6.80/2.40  tff(c_184, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_175])).
% 6.80/2.40  tff(c_196, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_184])).
% 6.80/2.40  tff(c_36, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.80/2.40  tff(c_83, plain, (![A_23]: (k2_relat_1(k6_partfun1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_36])).
% 6.80/2.40  tff(c_1031, plain, (![C_171, D_173, F_170, B_174, A_169, E_172]: (m1_subset_1(k1_partfun1(A_169, B_174, C_171, D_173, E_172, F_170), k1_zfmisc_1(k2_zfmisc_1(A_169, D_173))) | ~m1_subset_1(F_170, k1_zfmisc_1(k2_zfmisc_1(C_171, D_173))) | ~v1_funct_1(F_170) | ~m1_subset_1(E_172, k1_zfmisc_1(k2_zfmisc_1(A_169, B_174))) | ~v1_funct_1(E_172))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.80/2.40  tff(c_716, plain, (![D_122, C_123, A_124, B_125]: (D_122=C_123 | ~r2_relset_1(A_124, B_125, C_123, D_122) | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.80/2.40  tff(c_726, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_716])).
% 6.80/2.40  tff(c_745, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_726])).
% 6.80/2.40  tff(c_767, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_745])).
% 6.80/2.40  tff(c_1039, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1031, c_767])).
% 6.80/2.40  tff(c_1070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_1039])).
% 6.80/2.40  tff(c_1071, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_745])).
% 6.80/2.40  tff(c_1264, plain, (![B_205, E_200, D_203, C_202, F_204, A_201]: (k1_partfun1(A_201, B_205, C_202, D_203, E_200, F_204)=k5_relat_1(E_200, F_204) | ~m1_subset_1(F_204, k1_zfmisc_1(k2_zfmisc_1(C_202, D_203))) | ~v1_funct_1(F_204) | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_201, B_205))) | ~v1_funct_1(E_200))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.80/2.40  tff(c_1270, plain, (![A_201, B_205, E_200]: (k1_partfun1(A_201, B_205, '#skF_2', '#skF_1', E_200, '#skF_4')=k5_relat_1(E_200, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_201, B_205))) | ~v1_funct_1(E_200))), inference(resolution, [status(thm)], [c_70, c_1264])).
% 6.80/2.40  tff(c_1559, plain, (![A_239, B_240, E_241]: (k1_partfun1(A_239, B_240, '#skF_2', '#skF_1', E_241, '#skF_4')=k5_relat_1(E_241, '#skF_4') | ~m1_subset_1(E_241, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))) | ~v1_funct_1(E_241))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1270])).
% 6.80/2.40  tff(c_1571, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_1559])).
% 6.80/2.40  tff(c_1588, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1071, c_1571])).
% 6.80/2.40  tff(c_32, plain, (![A_20, B_22]: (r1_tarski(k2_relat_1(k5_relat_1(A_20, B_22)), k2_relat_1(B_22)) | ~v1_relat_1(B_22) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.80/2.40  tff(c_401, plain, (![B_100, A_101]: (r1_tarski(k2_relat_1(B_100), A_101) | ~v5_relat_1(B_100, A_101) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.80/2.40  tff(c_4, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.80/2.40  tff(c_1172, plain, (![B_192, A_193]: (k2_relat_1(B_192)=A_193 | ~r1_tarski(A_193, k2_relat_1(B_192)) | ~v5_relat_1(B_192, A_193) | ~v1_relat_1(B_192))), inference(resolution, [status(thm)], [c_401, c_4])).
% 6.80/2.40  tff(c_1202, plain, (![A_20, B_22]: (k2_relat_1(k5_relat_1(A_20, B_22))=k2_relat_1(B_22) | ~v5_relat_1(B_22, k2_relat_1(k5_relat_1(A_20, B_22))) | ~v1_relat_1(B_22) | ~v1_relat_1(A_20))), inference(resolution, [status(thm)], [c_32, c_1172])).
% 6.80/2.40  tff(c_1595, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_4'))=k2_relat_1('#skF_4') | ~v5_relat_1('#skF_4', k2_relat_1(k6_partfun1('#skF_1'))) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1588, c_1202])).
% 6.80/2.40  tff(c_1605, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_199, c_314, c_83, c_83, c_1588, c_1595])).
% 6.80/2.40  tff(c_362, plain, (![B_92, A_93]: (v5_relat_1(B_92, A_93) | ~r1_tarski(k2_relat_1(B_92), A_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.80/2.40  tff(c_377, plain, (![B_92]: (v5_relat_1(B_92, k2_relat_1(B_92)) | ~v1_relat_1(B_92))), inference(resolution, [status(thm)], [c_8, c_362])).
% 6.80/2.40  tff(c_464, plain, (![B_105]: (v2_funct_2(B_105, k2_relat_1(B_105)) | ~v5_relat_1(B_105, k2_relat_1(B_105)) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.80/2.40  tff(c_485, plain, (![B_92]: (v2_funct_2(B_92, k2_relat_1(B_92)) | ~v1_relat_1(B_92))), inference(resolution, [status(thm)], [c_377, c_464])).
% 6.80/2.40  tff(c_1626, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1605, c_485])).
% 6.80/2.40  tff(c_1647, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_1626])).
% 6.80/2.40  tff(c_1649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_656, c_1647])).
% 6.80/2.40  tff(c_1650, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_638])).
% 6.80/2.40  tff(c_26, plain, (![B_17, A_16]: (v5_relat_1(B_17, A_16) | ~r1_tarski(k2_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.80/2.40  tff(c_1670, plain, (![A_16]: (v5_relat_1('#skF_4', A_16) | ~r1_tarski('#skF_1', A_16) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1650, c_26])).
% 6.80/2.40  tff(c_2521, plain, (![A_311]: (v5_relat_1('#skF_4', A_311) | ~r1_tarski('#skF_1', A_311))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_1670])).
% 6.80/2.40  tff(c_12, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.80/2.40  tff(c_159, plain, (![B_68, A_69]: (~r1_xboole_0(B_68, A_69) | ~r1_tarski(B_68, A_69) | v1_xboole_0(B_68))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.80/2.40  tff(c_163, plain, (![A_5]: (~r1_tarski(A_5, k1_xboole_0) | v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_12, c_159])).
% 6.80/2.40  tff(c_424, plain, (![B_100]: (v1_xboole_0(k2_relat_1(B_100)) | ~v5_relat_1(B_100, k1_xboole_0) | ~v1_relat_1(B_100))), inference(resolution, [status(thm)], [c_401, c_163])).
% 6.80/2.40  tff(c_1655, plain, (v1_xboole_0('#skF_1') | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1650, c_424])).
% 6.80/2.40  tff(c_1674, plain, (v1_xboole_0('#skF_1') | ~v5_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_199, c_1655])).
% 6.80/2.40  tff(c_1717, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1674])).
% 6.80/2.40  tff(c_2536, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_2521, c_1717])).
% 6.80/2.40  tff(c_3175, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3163, c_2536])).
% 6.80/2.40  tff(c_3203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_3175])).
% 6.80/2.40  tff(c_3204, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_1674])).
% 6.80/2.40  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.80/2.40  tff(c_3209, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_3204, c_2])).
% 6.80/2.40  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.80/2.40  tff(c_3232, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3209, c_3209, c_18])).
% 6.80/2.40  tff(c_229, plain, (![B_78, A_79]: (v1_xboole_0(B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_79)) | ~v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.80/2.40  tff(c_247, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_229])).
% 6.80/2.40  tff(c_319, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_247])).
% 6.80/2.40  tff(c_3390, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3232, c_319])).
% 6.80/2.40  tff(c_3394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3204, c_3390])).
% 6.80/2.40  tff(c_3395, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_247])).
% 6.80/2.40  tff(c_3400, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_3395, c_2])).
% 6.80/2.40  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.80/2.40  tff(c_3413, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3400, c_3400, c_20])).
% 6.80/2.40  tff(c_3416, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3400, c_3400, c_18])).
% 6.80/2.40  tff(c_3396, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_247])).
% 6.80/2.40  tff(c_3404, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_3396, c_2])).
% 6.80/2.40  tff(c_3476, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3400, c_3404])).
% 6.80/2.40  tff(c_16, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.80/2.40  tff(c_3861, plain, (![B_438, A_439]: (B_438='#skF_4' | A_439='#skF_4' | k2_zfmisc_1(A_439, B_438)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3400, c_3400, c_3400, c_16])).
% 6.80/2.40  tff(c_3875, plain, ('#skF_1'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3476, c_3861])).
% 6.80/2.40  tff(c_3876, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_3875])).
% 6.80/2.40  tff(c_246, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_229])).
% 6.80/2.40  tff(c_274, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_246])).
% 6.80/2.40  tff(c_3883, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3876, c_274])).
% 6.80/2.40  tff(c_3891, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3395, c_3416, c_3883])).
% 6.80/2.40  tff(c_3892, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_3875])).
% 6.80/2.40  tff(c_3899, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3892, c_274])).
% 6.80/2.40  tff(c_3907, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3395, c_3413, c_3899])).
% 6.80/2.40  tff(c_3908, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_246])).
% 6.80/2.40  tff(c_3932, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3908, c_2])).
% 6.80/2.40  tff(c_164, plain, (![A_70]: (~r1_tarski(A_70, k1_xboole_0) | v1_xboole_0(A_70))), inference(resolution, [status(thm)], [c_12, c_159])).
% 6.80/2.40  tff(c_173, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_164])).
% 6.80/2.40  tff(c_149, plain, (![A_67]: (m1_subset_1(k6_partfun1(A_67), k1_zfmisc_1(k2_zfmisc_1(A_67, A_67))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_48])).
% 6.80/2.40  tff(c_153, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_149])).
% 6.80/2.40  tff(c_232, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_153, c_229])).
% 6.80/2.40  tff(c_244, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_232])).
% 6.80/2.40  tff(c_251, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_244, c_2])).
% 6.80/2.40  tff(c_268, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_251, c_82])).
% 6.80/2.40  tff(c_3933, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3932, c_268])).
% 6.80/2.40  tff(c_3945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_3933])).
% 6.80/2.40  tff(c_3946, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 6.80/2.40  tff(c_3980, plain, (![B_447, A_448]: (v1_relat_1(B_447) | ~m1_subset_1(B_447, k1_zfmisc_1(A_448)) | ~v1_relat_1(A_448))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.80/2.40  tff(c_3992, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_3980])).
% 6.80/2.40  tff(c_4004, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3992])).
% 6.80/2.40  tff(c_4165, plain, (![C_466, B_467, A_468]: (v5_relat_1(C_466, B_467) | ~m1_subset_1(C_466, k1_zfmisc_1(k2_zfmisc_1(A_468, B_467))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.80/2.40  tff(c_4184, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_4165])).
% 6.80/2.40  tff(c_3989, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_3980])).
% 6.80/2.40  tff(c_4001, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3989])).
% 6.80/2.40  tff(c_4660, plain, (![F_527, C_525, D_526, E_523, A_524, B_528]: (k1_partfun1(A_524, B_528, C_525, D_526, E_523, F_527)=k5_relat_1(E_523, F_527) | ~m1_subset_1(F_527, k1_zfmisc_1(k2_zfmisc_1(C_525, D_526))) | ~v1_funct_1(F_527) | ~m1_subset_1(E_523, k1_zfmisc_1(k2_zfmisc_1(A_524, B_528))) | ~v1_funct_1(E_523))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.80/2.40  tff(c_4666, plain, (![A_524, B_528, E_523]: (k1_partfun1(A_524, B_528, '#skF_2', '#skF_1', E_523, '#skF_4')=k5_relat_1(E_523, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_523, k1_zfmisc_1(k2_zfmisc_1(A_524, B_528))) | ~v1_funct_1(E_523))), inference(resolution, [status(thm)], [c_70, c_4660])).
% 6.80/2.40  tff(c_4834, plain, (![A_547, B_548, E_549]: (k1_partfun1(A_547, B_548, '#skF_2', '#skF_1', E_549, '#skF_4')=k5_relat_1(E_549, '#skF_4') | ~m1_subset_1(E_549, k1_zfmisc_1(k2_zfmisc_1(A_547, B_548))) | ~v1_funct_1(E_549))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4666])).
% 6.80/2.40  tff(c_4843, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_4834])).
% 6.80/2.40  tff(c_4857, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4843])).
% 6.80/2.40  tff(c_4866, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4857, c_54])).
% 6.80/2.40  tff(c_4870, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_4866])).
% 6.80/2.40  tff(c_4439, plain, (![D_496, C_497, A_498, B_499]: (D_496=C_497 | ~r2_relset_1(A_498, B_499, C_497, D_496) | ~m1_subset_1(D_496, k1_zfmisc_1(k2_zfmisc_1(A_498, B_499))) | ~m1_subset_1(C_497, k1_zfmisc_1(k2_zfmisc_1(A_498, B_499))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.80/2.40  tff(c_4449, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_4439])).
% 6.80/2.40  tff(c_4468, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_4449])).
% 6.80/2.40  tff(c_5165, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4870, c_4857, c_4857, c_4468])).
% 6.80/2.40  tff(c_5186, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5165, c_32])).
% 6.80/2.40  tff(c_5192, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4001, c_4004, c_83, c_5186])).
% 6.80/2.40  tff(c_4197, plain, (![B_473, A_474]: (r1_tarski(k2_relat_1(B_473), A_474) | ~v5_relat_1(B_473, A_474) | ~v1_relat_1(B_473))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.80/2.40  tff(c_4219, plain, (![B_473, A_474]: (k2_relat_1(B_473)=A_474 | ~r1_tarski(A_474, k2_relat_1(B_473)) | ~v5_relat_1(B_473, A_474) | ~v1_relat_1(B_473))), inference(resolution, [status(thm)], [c_4197, c_4])).
% 6.80/2.40  tff(c_5196, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_5192, c_4219])).
% 6.80/2.40  tff(c_5201, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4004, c_4184, c_5196])).
% 6.80/2.40  tff(c_4132, plain, (![B_461, A_462]: (v5_relat_1(B_461, A_462) | ~r1_tarski(k2_relat_1(B_461), A_462) | ~v1_relat_1(B_461))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.80/2.40  tff(c_4147, plain, (![B_461]: (v5_relat_1(B_461, k2_relat_1(B_461)) | ~v1_relat_1(B_461))), inference(resolution, [status(thm)], [c_8, c_4132])).
% 6.80/2.40  tff(c_4248, plain, (![B_479]: (v2_funct_2(B_479, k2_relat_1(B_479)) | ~v5_relat_1(B_479, k2_relat_1(B_479)) | ~v1_relat_1(B_479))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.80/2.40  tff(c_4262, plain, (![B_461]: (v2_funct_2(B_461, k2_relat_1(B_461)) | ~v1_relat_1(B_461))), inference(resolution, [status(thm)], [c_4147, c_4248])).
% 6.80/2.40  tff(c_5220, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5201, c_4262])).
% 6.80/2.40  tff(c_5241, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4004, c_5220])).
% 6.80/2.40  tff(c_5243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3946, c_5241])).
% 6.80/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.80/2.40  
% 6.80/2.40  Inference rules
% 6.80/2.40  ----------------------
% 6.80/2.40  #Ref     : 0
% 6.80/2.40  #Sup     : 1062
% 6.80/2.40  #Fact    : 0
% 6.80/2.40  #Define  : 0
% 6.80/2.40  #Split   : 23
% 6.80/2.40  #Chain   : 0
% 6.80/2.40  #Close   : 0
% 6.80/2.40  
% 6.80/2.40  Ordering : KBO
% 6.80/2.40  
% 6.80/2.40  Simplification rules
% 6.80/2.40  ----------------------
% 6.80/2.40  #Subsume      : 123
% 6.80/2.40  #Demod        : 1091
% 6.80/2.40  #Tautology    : 359
% 6.80/2.40  #SimpNegUnit  : 5
% 6.80/2.40  #BackRed      : 142
% 6.80/2.40  
% 6.80/2.40  #Partial instantiations: 0
% 6.80/2.40  #Strategies tried      : 1
% 6.80/2.40  
% 6.80/2.40  Timing (in seconds)
% 6.80/2.40  ----------------------
% 6.80/2.41  Preprocessing        : 0.41
% 6.80/2.41  Parsing              : 0.24
% 6.80/2.41  CNF conversion       : 0.03
% 6.80/2.41  Main loop            : 1.13
% 6.80/2.41  Inferencing          : 0.39
% 6.80/2.41  Reduction            : 0.41
% 6.80/2.41  Demodulation         : 0.30
% 6.80/2.41  BG Simplification    : 0.04
% 6.80/2.41  Subsumption          : 0.18
% 6.80/2.41  Abstraction          : 0.05
% 6.80/2.41  MUC search           : 0.00
% 6.80/2.41  Cooper               : 0.00
% 6.80/2.41  Total                : 1.61
% 6.80/2.41  Index Insertion      : 0.00
% 6.80/2.41  Index Deletion       : 0.00
% 6.80/2.41  Index Matching       : 0.00
% 6.80/2.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
