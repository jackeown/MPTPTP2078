%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:56 EST 2020

% Result     : Theorem 9.32s
% Output     : CNFRefutation 9.41s
% Verified   : 
% Statistics : Number of formulae       :  175 (2486 expanded)
%              Number of leaves         :   53 ( 901 expanded)
%              Depth                    :   31
%              Number of atoms          :  366 (8901 expanded)
%              Number of equality atoms :  100 (2173 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_211,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C
                & v2_funct_1(E) )
             => ( C = k1_xboole_0
                | k2_relset_1(A,B,D) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_135,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_149,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_141,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_189,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_179,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_145,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_167,axiom,(
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

tff(f_131,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_88,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_187,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_200,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_187])).

tff(c_92,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_84,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_38,plain,(
    ! [A_24] :
      ( v1_funct_1(k2_funct_1(A_24))
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_94,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_602,plain,(
    ! [A_139,B_140,C_141] :
      ( k2_relset_1(A_139,B_140,C_141) = k2_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_614,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_602])).

tff(c_80,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_616,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_80])).

tff(c_199,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_187])).

tff(c_234,plain,(
    ! [C_86,B_87,A_88] :
      ( v5_relat_1(C_86,B_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_246,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_94,c_234])).

tff(c_40,plain,(
    ! [A_24] :
      ( v1_relat_1(k2_funct_1(A_24))
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_247,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_234])).

tff(c_98,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_2068,plain,(
    ! [C_290,E_292,A_291,F_295,D_293,B_294] :
      ( k1_partfun1(A_291,B_294,C_290,D_293,E_292,F_295) = k5_relat_1(E_292,F_295)
      | ~ m1_subset_1(F_295,k1_zfmisc_1(k2_zfmisc_1(C_290,D_293)))
      | ~ v1_funct_1(F_295)
      | ~ m1_subset_1(E_292,k1_zfmisc_1(k2_zfmisc_1(A_291,B_294)))
      | ~ v1_funct_1(E_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_2075,plain,(
    ! [A_291,B_294,E_292] :
      ( k1_partfun1(A_291,B_294,'#skF_2','#skF_3',E_292,'#skF_5') = k5_relat_1(E_292,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_292,k1_zfmisc_1(k2_zfmisc_1(A_291,B_294)))
      | ~ v1_funct_1(E_292) ) ),
    inference(resolution,[status(thm)],[c_88,c_2068])).

tff(c_2423,plain,(
    ! [A_327,B_328,E_329] :
      ( k1_partfun1(A_327,B_328,'#skF_2','#skF_3',E_329,'#skF_5') = k5_relat_1(E_329,'#skF_5')
      | ~ m1_subset_1(E_329,k1_zfmisc_1(k2_zfmisc_1(A_327,B_328)))
      | ~ v1_funct_1(E_329) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2075])).

tff(c_2433,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_2423])).

tff(c_2441,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_2433])).

tff(c_86,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_2446,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2441,c_86])).

tff(c_74,plain,(
    ! [A_47,F_52,E_51,D_50,C_49,B_48] :
      ( m1_subset_1(k1_partfun1(A_47,B_48,C_49,D_50,E_51,F_52),k1_zfmisc_1(k2_zfmisc_1(A_47,D_50)))
      | ~ m1_subset_1(F_52,k1_zfmisc_1(k2_zfmisc_1(C_49,D_50)))
      | ~ v1_funct_1(F_52)
      | ~ m1_subset_1(E_51,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ v1_funct_1(E_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2450,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2441,c_74])).

tff(c_2454,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_94,c_92,c_88,c_2450])).

tff(c_60,plain,(
    ! [A_41,B_42,C_43] :
      ( k2_relset_1(A_41,B_42,C_43) = k2_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2481,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_2454,c_60])).

tff(c_2519,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2446,c_2481])).

tff(c_28,plain,(
    ! [A_18,B_20] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_18,B_20)),k2_relat_1(B_20))
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2637,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2519,c_28])).

tff(c_2679,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_200,c_2637])).

tff(c_409,plain,(
    ! [B_113,A_114] :
      ( r1_tarski(k2_relat_1(B_113),A_114)
      | ~ v5_relat_1(B_113,A_114)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_437,plain,(
    ! [B_113,A_114] :
      ( k2_relat_1(B_113) = A_114
      | ~ r1_tarski(A_114,k2_relat_1(B_113))
      | ~ v5_relat_1(B_113,A_114)
      | ~ v1_relat_1(B_113) ) ),
    inference(resolution,[status(thm)],[c_409,c_2])).

tff(c_2697,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2679,c_437])).

tff(c_2705,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_247,c_2697])).

tff(c_304,plain,(
    ! [C_101,A_102,B_103] :
      ( v4_relat_1(C_101,A_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_317,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_304])).

tff(c_26,plain,(
    ! [B_17,A_16] :
      ( k7_relat_1(B_17,A_16) = B_17
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_327,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_317,c_26])).

tff(c_330,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_327])).

tff(c_18,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_351,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_18])).

tff(c_357,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_351])).

tff(c_2711,plain,(
    k9_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2705,c_357])).

tff(c_1071,plain,(
    ! [B_197,A_198] :
      ( k10_relat_1(k2_funct_1(B_197),A_198) = k9_relat_1(B_197,A_198)
      | ~ v2_funct_1(B_197)
      | ~ v1_funct_1(B_197)
      | ~ v1_relat_1(B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k10_relat_1(B_14,A_13),k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3660,plain,(
    ! [B_356,A_357] :
      ( r1_tarski(k9_relat_1(B_356,A_357),k1_relat_1(k2_funct_1(B_356)))
      | ~ v1_relat_1(k2_funct_1(B_356))
      | ~ v2_funct_1(B_356)
      | ~ v1_funct_1(B_356)
      | ~ v1_relat_1(B_356) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1071,c_22])).

tff(c_3668,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2711,c_3660])).

tff(c_3700,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_92,c_84,c_3668])).

tff(c_3751,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3700])).

tff(c_3754,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_3751])).

tff(c_3758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_92,c_84,c_3754])).

tff(c_3760,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3700])).

tff(c_32,plain,(
    ! [A_21] : k2_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_90,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_579,plain,(
    ! [A_133,B_134,C_135] :
      ( k1_relset_1(A_133,B_134,C_135) = k1_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_592,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_579])).

tff(c_1596,plain,(
    ! [B_254,A_255,C_256] :
      ( k1_xboole_0 = B_254
      | k1_relset_1(A_255,B_254,C_256) = A_255
      | ~ v1_funct_2(C_256,A_255,B_254)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_255,B_254))) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1606,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_1596])).

tff(c_1613,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_592,c_1606])).

tff(c_1614,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1613])).

tff(c_50,plain,(
    ! [A_31] :
      ( k5_relat_1(A_31,k2_funct_1(A_31)) = k6_relat_1(k1_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_20,plain,(
    ! [B_12,A_10] :
      ( k9_relat_1(B_12,k2_relat_1(A_10)) = k2_relat_1(k5_relat_1(A_10,B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2740,plain,(
    ! [B_12] :
      ( k2_relat_1(k5_relat_1('#skF_5',B_12)) = k9_relat_1(B_12,'#skF_3')
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2705,c_20])).

tff(c_4122,plain,(
    ! [B_369] :
      ( k2_relat_1(k5_relat_1('#skF_5',B_369)) = k9_relat_1(B_369,'#skF_3')
      | ~ v1_relat_1(B_369) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_2740])).

tff(c_4211,plain,
    ( k2_relat_1(k6_relat_1(k1_relat_1('#skF_5'))) = k9_relat_1(k2_funct_1('#skF_5'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_4122])).

tff(c_4231,plain,(
    k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_92,c_84,c_3760,c_32,c_1614,c_4211])).

tff(c_3759,plain,(
    r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_3700])).

tff(c_24,plain,(
    ! [A_15] :
      ( k10_relat_1(A_15,k2_relat_1(A_15)) = k1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4295,plain,(
    ! [B_370] :
      ( k9_relat_1(B_370,k2_relat_1(k2_funct_1(B_370))) = k1_relat_1(k2_funct_1(B_370))
      | ~ v2_funct_1(B_370)
      | ~ v1_funct_1(B_370)
      | ~ v1_relat_1(B_370)
      | ~ v1_relat_1(k2_funct_1(B_370)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1071])).

tff(c_287,plain,(
    ! [B_99,A_100] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_99,A_100)),k2_relat_1(B_99))
      | ~ v1_relat_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_295,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k9_relat_1(B_9,A_8),k2_relat_1(B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_287])).

tff(c_2743,plain,(
    ! [A_8] :
      ( r1_tarski(k9_relat_1('#skF_5',A_8),'#skF_3')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2705,c_295])).

tff(c_2783,plain,(
    ! [A_8] : r1_tarski(k9_relat_1('#skF_5',A_8),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_200,c_2743])).

tff(c_4320,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4295,c_2783])).

tff(c_4383,plain,(
    r1_tarski(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3760,c_200,c_92,c_84,c_4320])).

tff(c_4386,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_4383,c_2])).

tff(c_4389,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3759,c_4386])).

tff(c_16,plain,(
    ! [A_7] :
      ( k9_relat_1(A_7,k1_relat_1(A_7)) = k2_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4403,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4389,c_16])).

tff(c_4414,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3760,c_4231,c_4403])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_316,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_94,c_304])).

tff(c_321,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_316,c_26])).

tff(c_324,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_321])).

tff(c_337,plain,
    ( k9_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_18])).

tff(c_343,plain,(
    k9_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_337])).

tff(c_665,plain,(
    ! [B_147,A_148] :
      ( k9_relat_1(B_147,k2_relat_1(A_148)) = k2_relat_1(k5_relat_1(A_148,B_147))
      | ~ v1_relat_1(B_147)
      | ~ v1_relat_1(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6928,plain,(
    ! [B_426,A_427,B_428] :
      ( k2_relat_1(k5_relat_1(k7_relat_1(B_426,A_427),B_428)) = k9_relat_1(B_428,k9_relat_1(B_426,A_427))
      | ~ v1_relat_1(B_428)
      | ~ v1_relat_1(k7_relat_1(B_426,A_427))
      | ~ v1_relat_1(B_426) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_665])).

tff(c_7059,plain,(
    ! [B_428] :
      ( k9_relat_1(B_428,k9_relat_1('#skF_4','#skF_1')) = k2_relat_1(k5_relat_1('#skF_4',B_428))
      | ~ v1_relat_1(B_428)
      | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_1'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_6928])).

tff(c_7091,plain,(
    ! [B_429] :
      ( k9_relat_1(B_429,k2_relat_1('#skF_4')) = k2_relat_1(k5_relat_1('#skF_4',B_429))
      | ~ v1_relat_1(B_429) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_199,c_324,c_343,c_7059])).

tff(c_266,plain,(
    ! [B_95,A_96] :
      ( v5_relat_1(B_95,A_96)
      | ~ r1_tarski(k2_relat_1(B_95),A_96)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2976,plain,(
    ! [B_338,A_339,A_340] :
      ( v5_relat_1(k7_relat_1(B_338,A_339),A_340)
      | ~ r1_tarski(k9_relat_1(B_338,A_339),A_340)
      | ~ v1_relat_1(k7_relat_1(B_338,A_339))
      | ~ v1_relat_1(B_338) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_266])).

tff(c_3004,plain,(
    ! [A_340] :
      ( v5_relat_1('#skF_5',A_340)
      | ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),A_340)
      | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_2976])).

tff(c_3021,plain,(
    ! [A_341] :
      ( v5_relat_1('#skF_5',A_341)
      | ~ r1_tarski('#skF_3',A_341) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_200,c_330,c_2711,c_3004])).

tff(c_904,plain,(
    ! [B_187,A_188] :
      ( k2_relat_1(B_187) = A_188
      | ~ r1_tarski(A_188,k2_relat_1(B_187))
      | ~ v5_relat_1(B_187,A_188)
      | ~ v1_relat_1(B_187) ) ),
    inference(resolution,[status(thm)],[c_409,c_2])).

tff(c_942,plain,(
    ! [B_9,A_8] :
      ( k9_relat_1(B_9,A_8) = k2_relat_1(B_9)
      | ~ v5_relat_1(B_9,k9_relat_1(B_9,A_8))
      | ~ v1_relat_1(B_9) ) ),
    inference(resolution,[status(thm)],[c_295,c_904])).

tff(c_3032,plain,(
    ! [A_8] :
      ( k9_relat_1('#skF_5',A_8) = k2_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_3',k9_relat_1('#skF_5',A_8)) ) ),
    inference(resolution,[status(thm)],[c_3021,c_942])).

tff(c_3050,plain,(
    ! [A_8] :
      ( k9_relat_1('#skF_5',A_8) = '#skF_3'
      | ~ r1_tarski('#skF_3',k9_relat_1('#skF_5',A_8)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_2705,c_3032])).

tff(c_7112,plain,
    ( k9_relat_1('#skF_5',k2_relat_1('#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7091,c_3050])).

tff(c_7198,plain,(
    k9_relat_1('#skF_5',k2_relat_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_6,c_2519,c_7112])).

tff(c_44,plain,(
    ! [B_28,A_27] :
      ( k10_relat_1(k2_funct_1(B_28),A_27) = k9_relat_1(B_28,A_27)
      | ~ v2_funct_1(B_28)
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_146,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(k10_relat_1(B_69,A_70),k1_relat_1(B_69))
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_152,plain,(
    ! [B_69,A_70] :
      ( k10_relat_1(B_69,A_70) = k1_relat_1(B_69)
      | ~ r1_tarski(k1_relat_1(B_69),k10_relat_1(B_69,A_70))
      | ~ v1_relat_1(B_69) ) ),
    inference(resolution,[status(thm)],[c_146,c_2])).

tff(c_4400,plain,(
    ! [A_70] :
      ( k10_relat_1(k2_funct_1('#skF_5'),A_70) = k1_relat_1(k2_funct_1('#skF_5'))
      | ~ r1_tarski('#skF_3',k10_relat_1(k2_funct_1('#skF_5'),A_70))
      | ~ v1_relat_1(k2_funct_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4389,c_152])).

tff(c_10862,plain,(
    ! [A_574] :
      ( k10_relat_1(k2_funct_1('#skF_5'),A_574) = '#skF_3'
      | ~ r1_tarski('#skF_3',k10_relat_1(k2_funct_1('#skF_5'),A_574)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3760,c_4389,c_4400])).

tff(c_10873,plain,(
    ! [A_27] :
      ( k10_relat_1(k2_funct_1('#skF_5'),A_27) = '#skF_3'
      | ~ r1_tarski('#skF_3',k9_relat_1('#skF_5',A_27))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_10862])).

tff(c_10887,plain,(
    ! [A_580] :
      ( k10_relat_1(k2_funct_1('#skF_5'),A_580) = '#skF_3'
      | ~ r1_tarski('#skF_3',k9_relat_1('#skF_5',A_580)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_92,c_84,c_10873])).

tff(c_10890,plain,
    ( k10_relat_1(k2_funct_1('#skF_5'),k2_relat_1('#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7198,c_10887])).

tff(c_10934,plain,(
    k10_relat_1(k2_funct_1('#skF_5'),k2_relat_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10890])).

tff(c_14,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k2_relat_1(B_6),A_5)
      | ~ v5_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1189,plain,(
    ! [B_210,A_211] :
      ( k9_relat_1(B_210,k10_relat_1(B_210,A_211)) = A_211
      | ~ r1_tarski(A_211,k2_relat_1(B_210))
      | ~ v1_funct_1(B_210)
      | ~ v1_relat_1(B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1226,plain,(
    ! [B_210,B_6] :
      ( k9_relat_1(B_210,k10_relat_1(B_210,k2_relat_1(B_6))) = k2_relat_1(B_6)
      | ~ v1_funct_1(B_210)
      | ~ v1_relat_1(B_210)
      | ~ v5_relat_1(B_6,k2_relat_1(B_210))
      | ~ v1_relat_1(B_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_1189])).

tff(c_10961,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = k2_relat_1('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v5_relat_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10934,c_1226])).

tff(c_10981,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_246,c_4414,c_3760,c_4231,c_10961])).

tff(c_10982,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_616,c_10981])).

tff(c_10995,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_10982])).

tff(c_10999,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_92,c_84,c_10995])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:00:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.32/3.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.32/3.53  
% 9.32/3.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.41/3.54  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.41/3.54  
% 9.41/3.54  %Foreground sorts:
% 9.41/3.54  
% 9.41/3.54  
% 9.41/3.54  %Background operators:
% 9.41/3.54  
% 9.41/3.54  
% 9.41/3.54  %Foreground operators:
% 9.41/3.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.41/3.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.41/3.54  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.41/3.54  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.41/3.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.41/3.54  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.41/3.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.41/3.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.41/3.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.41/3.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.41/3.54  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.41/3.54  tff('#skF_5', type, '#skF_5': $i).
% 9.41/3.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.41/3.54  tff('#skF_2', type, '#skF_2': $i).
% 9.41/3.54  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.41/3.54  tff('#skF_3', type, '#skF_3': $i).
% 9.41/3.54  tff('#skF_1', type, '#skF_1': $i).
% 9.41/3.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.41/3.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.41/3.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.41/3.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.41/3.54  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.41/3.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.41/3.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.41/3.54  tff('#skF_4', type, '#skF_4': $i).
% 9.41/3.54  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.41/3.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.41/3.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.41/3.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.41/3.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.41/3.54  
% 9.41/3.56  tff(f_211, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 9.41/3.56  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.41/3.56  tff(f_97, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 9.41/3.56  tff(f_149, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.41/3.56  tff(f_141, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.41/3.56  tff(f_189, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.41/3.56  tff(f_179, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.41/3.56  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 9.41/3.56  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 9.41/3.56  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.41/3.56  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 9.41/3.56  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 9.41/3.56  tff(f_113, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 9.41/3.56  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 9.41/3.56  tff(f_81, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 9.41/3.56  tff(f_145, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.41/3.56  tff(f_167, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.41/3.56  tff(f_131, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 9.41/3.56  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 9.41/3.56  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 9.41/3.56  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_relat_1)).
% 9.41/3.56  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 9.41/3.56  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 9.41/3.56  tff(c_88, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_211])).
% 9.41/3.56  tff(c_187, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.41/3.56  tff(c_200, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_187])).
% 9.41/3.56  tff(c_92, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_211])).
% 9.41/3.56  tff(c_84, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_211])).
% 9.41/3.56  tff(c_38, plain, (![A_24]: (v1_funct_1(k2_funct_1(A_24)) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.41/3.56  tff(c_94, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_211])).
% 9.41/3.56  tff(c_602, plain, (![A_139, B_140, C_141]: (k2_relset_1(A_139, B_140, C_141)=k2_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.41/3.56  tff(c_614, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_94, c_602])).
% 9.41/3.56  tff(c_80, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_211])).
% 9.41/3.56  tff(c_616, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_614, c_80])).
% 9.41/3.56  tff(c_199, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_94, c_187])).
% 9.41/3.56  tff(c_234, plain, (![C_86, B_87, A_88]: (v5_relat_1(C_86, B_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.41/3.56  tff(c_246, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_94, c_234])).
% 9.41/3.56  tff(c_40, plain, (![A_24]: (v1_relat_1(k2_funct_1(A_24)) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.41/3.56  tff(c_247, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_88, c_234])).
% 9.41/3.56  tff(c_98, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_211])).
% 9.41/3.56  tff(c_2068, plain, (![C_290, E_292, A_291, F_295, D_293, B_294]: (k1_partfun1(A_291, B_294, C_290, D_293, E_292, F_295)=k5_relat_1(E_292, F_295) | ~m1_subset_1(F_295, k1_zfmisc_1(k2_zfmisc_1(C_290, D_293))) | ~v1_funct_1(F_295) | ~m1_subset_1(E_292, k1_zfmisc_1(k2_zfmisc_1(A_291, B_294))) | ~v1_funct_1(E_292))), inference(cnfTransformation, [status(thm)], [f_189])).
% 9.41/3.56  tff(c_2075, plain, (![A_291, B_294, E_292]: (k1_partfun1(A_291, B_294, '#skF_2', '#skF_3', E_292, '#skF_5')=k5_relat_1(E_292, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_292, k1_zfmisc_1(k2_zfmisc_1(A_291, B_294))) | ~v1_funct_1(E_292))), inference(resolution, [status(thm)], [c_88, c_2068])).
% 9.41/3.56  tff(c_2423, plain, (![A_327, B_328, E_329]: (k1_partfun1(A_327, B_328, '#skF_2', '#skF_3', E_329, '#skF_5')=k5_relat_1(E_329, '#skF_5') | ~m1_subset_1(E_329, k1_zfmisc_1(k2_zfmisc_1(A_327, B_328))) | ~v1_funct_1(E_329))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_2075])).
% 9.41/3.56  tff(c_2433, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_94, c_2423])).
% 9.41/3.56  tff(c_2441, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_2433])).
% 9.41/3.56  tff(c_86, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_211])).
% 9.41/3.56  tff(c_2446, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2441, c_86])).
% 9.41/3.56  tff(c_74, plain, (![A_47, F_52, E_51, D_50, C_49, B_48]: (m1_subset_1(k1_partfun1(A_47, B_48, C_49, D_50, E_51, F_52), k1_zfmisc_1(k2_zfmisc_1(A_47, D_50))) | ~m1_subset_1(F_52, k1_zfmisc_1(k2_zfmisc_1(C_49, D_50))) | ~v1_funct_1(F_52) | ~m1_subset_1(E_51, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~v1_funct_1(E_51))), inference(cnfTransformation, [status(thm)], [f_179])).
% 9.41/3.56  tff(c_2450, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2441, c_74])).
% 9.41/3.56  tff(c_2454, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_94, c_92, c_88, c_2450])).
% 9.41/3.56  tff(c_60, plain, (![A_41, B_42, C_43]: (k2_relset_1(A_41, B_42, C_43)=k2_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.41/3.56  tff(c_2481, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_2454, c_60])).
% 9.41/3.56  tff(c_2519, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2446, c_2481])).
% 9.41/3.56  tff(c_28, plain, (![A_18, B_20]: (r1_tarski(k2_relat_1(k5_relat_1(A_18, B_20)), k2_relat_1(B_20)) | ~v1_relat_1(B_20) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.41/3.56  tff(c_2637, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2519, c_28])).
% 9.41/3.56  tff(c_2679, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_200, c_2637])).
% 9.41/3.56  tff(c_409, plain, (![B_113, A_114]: (r1_tarski(k2_relat_1(B_113), A_114) | ~v5_relat_1(B_113, A_114) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.41/3.56  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.41/3.56  tff(c_437, plain, (![B_113, A_114]: (k2_relat_1(B_113)=A_114 | ~r1_tarski(A_114, k2_relat_1(B_113)) | ~v5_relat_1(B_113, A_114) | ~v1_relat_1(B_113))), inference(resolution, [status(thm)], [c_409, c_2])).
% 9.41/3.56  tff(c_2697, plain, (k2_relat_1('#skF_5')='#skF_3' | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2679, c_437])).
% 9.41/3.56  tff(c_2705, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_200, c_247, c_2697])).
% 9.41/3.56  tff(c_304, plain, (![C_101, A_102, B_103]: (v4_relat_1(C_101, A_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.41/3.56  tff(c_317, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_88, c_304])).
% 9.41/3.56  tff(c_26, plain, (![B_17, A_16]: (k7_relat_1(B_17, A_16)=B_17 | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.41/3.56  tff(c_327, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_317, c_26])).
% 9.41/3.56  tff(c_330, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_200, c_327])).
% 9.41/3.56  tff(c_18, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.41/3.56  tff(c_351, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_330, c_18])).
% 9.41/3.56  tff(c_357, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_351])).
% 9.41/3.56  tff(c_2711, plain, (k9_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2705, c_357])).
% 9.41/3.56  tff(c_1071, plain, (![B_197, A_198]: (k10_relat_1(k2_funct_1(B_197), A_198)=k9_relat_1(B_197, A_198) | ~v2_funct_1(B_197) | ~v1_funct_1(B_197) | ~v1_relat_1(B_197))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.41/3.56  tff(c_22, plain, (![B_14, A_13]: (r1_tarski(k10_relat_1(B_14, A_13), k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.41/3.56  tff(c_3660, plain, (![B_356, A_357]: (r1_tarski(k9_relat_1(B_356, A_357), k1_relat_1(k2_funct_1(B_356))) | ~v1_relat_1(k2_funct_1(B_356)) | ~v2_funct_1(B_356) | ~v1_funct_1(B_356) | ~v1_relat_1(B_356))), inference(superposition, [status(thm), theory('equality')], [c_1071, c_22])).
% 9.41/3.56  tff(c_3668, plain, (r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2711, c_3660])).
% 9.41/3.56  tff(c_3700, plain, (r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_92, c_84, c_3668])).
% 9.41/3.56  tff(c_3751, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_3700])).
% 9.41/3.56  tff(c_3754, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_3751])).
% 9.41/3.56  tff(c_3758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_200, c_92, c_84, c_3754])).
% 9.41/3.56  tff(c_3760, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_3700])).
% 9.41/3.56  tff(c_32, plain, (![A_21]: (k2_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.41/3.56  tff(c_82, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_211])).
% 9.41/3.56  tff(c_90, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_211])).
% 9.41/3.56  tff(c_579, plain, (![A_133, B_134, C_135]: (k1_relset_1(A_133, B_134, C_135)=k1_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 9.41/3.56  tff(c_592, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_579])).
% 9.41/3.56  tff(c_1596, plain, (![B_254, A_255, C_256]: (k1_xboole_0=B_254 | k1_relset_1(A_255, B_254, C_256)=A_255 | ~v1_funct_2(C_256, A_255, B_254) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_255, B_254))))), inference(cnfTransformation, [status(thm)], [f_167])).
% 9.41/3.56  tff(c_1606, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_88, c_1596])).
% 9.41/3.56  tff(c_1613, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_592, c_1606])).
% 9.41/3.56  tff(c_1614, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_82, c_1613])).
% 9.41/3.56  tff(c_50, plain, (![A_31]: (k5_relat_1(A_31, k2_funct_1(A_31))=k6_relat_1(k1_relat_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.41/3.56  tff(c_20, plain, (![B_12, A_10]: (k9_relat_1(B_12, k2_relat_1(A_10))=k2_relat_1(k5_relat_1(A_10, B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.41/3.56  tff(c_2740, plain, (![B_12]: (k2_relat_1(k5_relat_1('#skF_5', B_12))=k9_relat_1(B_12, '#skF_3') | ~v1_relat_1(B_12) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2705, c_20])).
% 9.41/3.56  tff(c_4122, plain, (![B_369]: (k2_relat_1(k5_relat_1('#skF_5', B_369))=k9_relat_1(B_369, '#skF_3') | ~v1_relat_1(B_369))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_2740])).
% 9.41/3.56  tff(c_4211, plain, (k2_relat_1(k6_relat_1(k1_relat_1('#skF_5')))=k9_relat_1(k2_funct_1('#skF_5'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_50, c_4122])).
% 9.41/3.56  tff(c_4231, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_200, c_92, c_84, c_3760, c_32, c_1614, c_4211])).
% 9.41/3.56  tff(c_3759, plain, (r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_5')))), inference(splitRight, [status(thm)], [c_3700])).
% 9.41/3.56  tff(c_24, plain, (![A_15]: (k10_relat_1(A_15, k2_relat_1(A_15))=k1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.41/3.56  tff(c_4295, plain, (![B_370]: (k9_relat_1(B_370, k2_relat_1(k2_funct_1(B_370)))=k1_relat_1(k2_funct_1(B_370)) | ~v2_funct_1(B_370) | ~v1_funct_1(B_370) | ~v1_relat_1(B_370) | ~v1_relat_1(k2_funct_1(B_370)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1071])).
% 9.41/3.56  tff(c_287, plain, (![B_99, A_100]: (r1_tarski(k2_relat_1(k7_relat_1(B_99, A_100)), k2_relat_1(B_99)) | ~v1_relat_1(B_99))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.41/3.56  tff(c_295, plain, (![B_9, A_8]: (r1_tarski(k9_relat_1(B_9, A_8), k2_relat_1(B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(B_9))), inference(superposition, [status(thm), theory('equality')], [c_18, c_287])).
% 9.41/3.56  tff(c_2743, plain, (![A_8]: (r1_tarski(k9_relat_1('#skF_5', A_8), '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2705, c_295])).
% 9.41/3.56  tff(c_2783, plain, (![A_8]: (r1_tarski(k9_relat_1('#skF_5', A_8), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_200, c_2743])).
% 9.41/3.56  tff(c_4320, plain, (r1_tarski(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4295, c_2783])).
% 9.41/3.56  tff(c_4383, plain, (r1_tarski(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3760, c_200, c_92, c_84, c_4320])).
% 9.41/3.56  tff(c_4386, plain, (k1_relat_1(k2_funct_1('#skF_5'))='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_5')))), inference(resolution, [status(thm)], [c_4383, c_2])).
% 9.41/3.56  tff(c_4389, plain, (k1_relat_1(k2_funct_1('#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3759, c_4386])).
% 9.41/3.56  tff(c_16, plain, (![A_7]: (k9_relat_1(A_7, k1_relat_1(A_7))=k2_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.41/3.56  tff(c_4403, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4389, c_16])).
% 9.41/3.56  tff(c_4414, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3760, c_4231, c_4403])).
% 9.41/3.56  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.41/3.56  tff(c_316, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_94, c_304])).
% 9.41/3.56  tff(c_321, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_316, c_26])).
% 9.41/3.56  tff(c_324, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_199, c_321])).
% 9.41/3.56  tff(c_337, plain, (k9_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_324, c_18])).
% 9.41/3.56  tff(c_343, plain, (k9_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_337])).
% 9.41/3.56  tff(c_665, plain, (![B_147, A_148]: (k9_relat_1(B_147, k2_relat_1(A_148))=k2_relat_1(k5_relat_1(A_148, B_147)) | ~v1_relat_1(B_147) | ~v1_relat_1(A_148))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.41/3.56  tff(c_6928, plain, (![B_426, A_427, B_428]: (k2_relat_1(k5_relat_1(k7_relat_1(B_426, A_427), B_428))=k9_relat_1(B_428, k9_relat_1(B_426, A_427)) | ~v1_relat_1(B_428) | ~v1_relat_1(k7_relat_1(B_426, A_427)) | ~v1_relat_1(B_426))), inference(superposition, [status(thm), theory('equality')], [c_18, c_665])).
% 9.41/3.56  tff(c_7059, plain, (![B_428]: (k9_relat_1(B_428, k9_relat_1('#skF_4', '#skF_1'))=k2_relat_1(k5_relat_1('#skF_4', B_428)) | ~v1_relat_1(B_428) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_1')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_324, c_6928])).
% 9.41/3.56  tff(c_7091, plain, (![B_429]: (k9_relat_1(B_429, k2_relat_1('#skF_4'))=k2_relat_1(k5_relat_1('#skF_4', B_429)) | ~v1_relat_1(B_429))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_199, c_324, c_343, c_7059])).
% 9.41/3.56  tff(c_266, plain, (![B_95, A_96]: (v5_relat_1(B_95, A_96) | ~r1_tarski(k2_relat_1(B_95), A_96) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.41/3.56  tff(c_2976, plain, (![B_338, A_339, A_340]: (v5_relat_1(k7_relat_1(B_338, A_339), A_340) | ~r1_tarski(k9_relat_1(B_338, A_339), A_340) | ~v1_relat_1(k7_relat_1(B_338, A_339)) | ~v1_relat_1(B_338))), inference(superposition, [status(thm), theory('equality')], [c_18, c_266])).
% 9.41/3.56  tff(c_3004, plain, (![A_340]: (v5_relat_1('#skF_5', A_340) | ~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), A_340) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_330, c_2976])).
% 9.41/3.56  tff(c_3021, plain, (![A_341]: (v5_relat_1('#skF_5', A_341) | ~r1_tarski('#skF_3', A_341))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_200, c_330, c_2711, c_3004])).
% 9.41/3.56  tff(c_904, plain, (![B_187, A_188]: (k2_relat_1(B_187)=A_188 | ~r1_tarski(A_188, k2_relat_1(B_187)) | ~v5_relat_1(B_187, A_188) | ~v1_relat_1(B_187))), inference(resolution, [status(thm)], [c_409, c_2])).
% 9.41/3.56  tff(c_942, plain, (![B_9, A_8]: (k9_relat_1(B_9, A_8)=k2_relat_1(B_9) | ~v5_relat_1(B_9, k9_relat_1(B_9, A_8)) | ~v1_relat_1(B_9))), inference(resolution, [status(thm)], [c_295, c_904])).
% 9.41/3.56  tff(c_3032, plain, (![A_8]: (k9_relat_1('#skF_5', A_8)=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r1_tarski('#skF_3', k9_relat_1('#skF_5', A_8)))), inference(resolution, [status(thm)], [c_3021, c_942])).
% 9.41/3.56  tff(c_3050, plain, (![A_8]: (k9_relat_1('#skF_5', A_8)='#skF_3' | ~r1_tarski('#skF_3', k9_relat_1('#skF_5', A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_2705, c_3032])).
% 9.41/3.56  tff(c_7112, plain, (k9_relat_1('#skF_5', k2_relat_1('#skF_4'))='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7091, c_3050])).
% 9.41/3.56  tff(c_7198, plain, (k9_relat_1('#skF_5', k2_relat_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_200, c_6, c_2519, c_7112])).
% 9.41/3.56  tff(c_44, plain, (![B_28, A_27]: (k10_relat_1(k2_funct_1(B_28), A_27)=k9_relat_1(B_28, A_27) | ~v2_funct_1(B_28) | ~v1_funct_1(B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.41/3.56  tff(c_146, plain, (![B_69, A_70]: (r1_tarski(k10_relat_1(B_69, A_70), k1_relat_1(B_69)) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.41/3.56  tff(c_152, plain, (![B_69, A_70]: (k10_relat_1(B_69, A_70)=k1_relat_1(B_69) | ~r1_tarski(k1_relat_1(B_69), k10_relat_1(B_69, A_70)) | ~v1_relat_1(B_69))), inference(resolution, [status(thm)], [c_146, c_2])).
% 9.41/3.56  tff(c_4400, plain, (![A_70]: (k10_relat_1(k2_funct_1('#skF_5'), A_70)=k1_relat_1(k2_funct_1('#skF_5')) | ~r1_tarski('#skF_3', k10_relat_1(k2_funct_1('#skF_5'), A_70)) | ~v1_relat_1(k2_funct_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_4389, c_152])).
% 9.41/3.56  tff(c_10862, plain, (![A_574]: (k10_relat_1(k2_funct_1('#skF_5'), A_574)='#skF_3' | ~r1_tarski('#skF_3', k10_relat_1(k2_funct_1('#skF_5'), A_574)))), inference(demodulation, [status(thm), theory('equality')], [c_3760, c_4389, c_4400])).
% 9.41/3.56  tff(c_10873, plain, (![A_27]: (k10_relat_1(k2_funct_1('#skF_5'), A_27)='#skF_3' | ~r1_tarski('#skF_3', k9_relat_1('#skF_5', A_27)) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_10862])).
% 9.41/3.56  tff(c_10887, plain, (![A_580]: (k10_relat_1(k2_funct_1('#skF_5'), A_580)='#skF_3' | ~r1_tarski('#skF_3', k9_relat_1('#skF_5', A_580)))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_92, c_84, c_10873])).
% 9.41/3.56  tff(c_10890, plain, (k10_relat_1(k2_funct_1('#skF_5'), k2_relat_1('#skF_4'))='#skF_3' | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7198, c_10887])).
% 9.41/3.56  tff(c_10934, plain, (k10_relat_1(k2_funct_1('#skF_5'), k2_relat_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10890])).
% 9.41/3.56  tff(c_14, plain, (![B_6, A_5]: (r1_tarski(k2_relat_1(B_6), A_5) | ~v5_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.41/3.56  tff(c_1189, plain, (![B_210, A_211]: (k9_relat_1(B_210, k10_relat_1(B_210, A_211))=A_211 | ~r1_tarski(A_211, k2_relat_1(B_210)) | ~v1_funct_1(B_210) | ~v1_relat_1(B_210))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.41/3.56  tff(c_1226, plain, (![B_210, B_6]: (k9_relat_1(B_210, k10_relat_1(B_210, k2_relat_1(B_6)))=k2_relat_1(B_6) | ~v1_funct_1(B_210) | ~v1_relat_1(B_210) | ~v5_relat_1(B_6, k2_relat_1(B_210)) | ~v1_relat_1(B_6))), inference(resolution, [status(thm)], [c_14, c_1189])).
% 9.41/3.56  tff(c_10961, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')=k2_relat_1('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v5_relat_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10934, c_1226])).
% 9.41/3.56  tff(c_10981, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_246, c_4414, c_3760, c_4231, c_10961])).
% 9.41/3.56  tff(c_10982, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_616, c_10981])).
% 9.41/3.56  tff(c_10995, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_10982])).
% 9.41/3.56  tff(c_10999, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_200, c_92, c_84, c_10995])).
% 9.41/3.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.41/3.56  
% 9.41/3.56  Inference rules
% 9.41/3.56  ----------------------
% 9.41/3.56  #Ref     : 0
% 9.41/3.56  #Sup     : 2326
% 9.41/3.56  #Fact    : 0
% 9.41/3.56  #Define  : 0
% 9.41/3.56  #Split   : 11
% 9.41/3.56  #Chain   : 0
% 9.41/3.56  #Close   : 0
% 9.41/3.56  
% 9.41/3.56  Ordering : KBO
% 9.41/3.56  
% 9.41/3.56  Simplification rules
% 9.41/3.56  ----------------------
% 9.41/3.56  #Subsume      : 187
% 9.41/3.56  #Demod        : 2720
% 9.41/3.56  #Tautology    : 742
% 9.41/3.56  #SimpNegUnit  : 16
% 9.41/3.56  #BackRed      : 20
% 9.41/3.56  
% 9.41/3.56  #Partial instantiations: 0
% 9.41/3.56  #Strategies tried      : 1
% 9.41/3.56  
% 9.41/3.56  Timing (in seconds)
% 9.41/3.56  ----------------------
% 9.41/3.57  Preprocessing        : 0.37
% 9.41/3.57  Parsing              : 0.19
% 9.41/3.57  CNF conversion       : 0.03
% 9.41/3.57  Main loop            : 2.29
% 9.41/3.57  Inferencing          : 0.65
% 9.41/3.57  Reduction            : 0.99
% 9.41/3.57  Demodulation         : 0.78
% 9.41/3.57  BG Simplification    : 0.07
% 9.41/3.57  Subsumption          : 0.44
% 9.41/3.57  Abstraction          : 0.08
% 9.41/3.57  MUC search           : 0.00
% 9.41/3.57  Cooper               : 0.00
% 9.41/3.57  Total                : 2.72
% 9.41/3.57  Index Insertion      : 0.00
% 9.41/3.57  Index Deletion       : 0.00
% 9.41/3.57  Index Matching       : 0.00
% 9.41/3.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
