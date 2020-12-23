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
% DateTime   : Thu Dec  3 10:13:13 EST 2020

% Result     : Theorem 22.69s
% Output     : CNFRefutation 22.69s
% Verified   : 
% Statistics : Number of formulae       :  262 (4210 expanded)
%              Number of leaves         :   62 (1500 expanded)
%              Depth                    :   20
%              Number of atoms          :  633 (16093 expanded)
%              Number of equality atoms :  191 (4302 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_362,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_320,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_259,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_111,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_257,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_243,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_247,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_205,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_304,axiom,(
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

tff(f_99,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_193,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_231,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_278,axiom,(
    ! [A,B,C] :
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

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_107,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_83,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_140,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_197,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_223,axiom,(
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

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_187,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_336,axiom,(
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

tff(f_81,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_170,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
          & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

tff(c_130,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_362])).

tff(c_12,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_142,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_362])).

tff(c_302,plain,(
    ! [B_106,A_107] :
      ( v1_relat_1(B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_107))
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_308,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_142,c_302])).

tff(c_317,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_308])).

tff(c_146,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_362])).

tff(c_144,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_362])).

tff(c_51409,plain,(
    ! [C_1948,A_1949,B_1950] :
      ( v1_funct_1(k2_funct_1(C_1948))
      | k2_relset_1(A_1949,B_1950,C_1948) != B_1950
      | ~ v2_funct_1(C_1948)
      | ~ m1_subset_1(C_1948,k1_zfmisc_1(k2_zfmisc_1(A_1949,B_1950)))
      | ~ v1_funct_2(C_1948,A_1949,B_1950)
      | ~ v1_funct_1(C_1948) ) ),
    inference(cnfTransformation,[status(thm)],[f_320])).

tff(c_51415,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_142,c_51409])).

tff(c_51424,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_144,c_51415])).

tff(c_51460,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_51424])).

tff(c_134,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_362])).

tff(c_152,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_362])).

tff(c_150,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_362])).

tff(c_148,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_362])).

tff(c_106,plain,(
    ! [A_68] : k6_relat_1(A_68) = k6_partfun1(A_68) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_48,plain,(
    ! [A_26] : v2_funct_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_155,plain,(
    ! [A_26] : v2_funct_1(k6_partfun1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_48])).

tff(c_140,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_362])).

tff(c_51894,plain,(
    ! [A_1977,E_1975,B_1978,C_1976,D_1980,F_1979] :
      ( k1_partfun1(A_1977,B_1978,C_1976,D_1980,E_1975,F_1979) = k5_relat_1(E_1975,F_1979)
      | ~ m1_subset_1(F_1979,k1_zfmisc_1(k2_zfmisc_1(C_1976,D_1980)))
      | ~ v1_funct_1(F_1979)
      | ~ m1_subset_1(E_1975,k1_zfmisc_1(k2_zfmisc_1(A_1977,B_1978)))
      | ~ v1_funct_1(E_1975) ) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_51900,plain,(
    ! [A_1977,B_1978,E_1975] :
      ( k1_partfun1(A_1977,B_1978,'#skF_2','#skF_1',E_1975,'#skF_4') = k5_relat_1(E_1975,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_1975,k1_zfmisc_1(k2_zfmisc_1(A_1977,B_1978)))
      | ~ v1_funct_1(E_1975) ) ),
    inference(resolution,[status(thm)],[c_142,c_51894])).

tff(c_52012,plain,(
    ! [A_1983,B_1984,E_1985] :
      ( k1_partfun1(A_1983,B_1984,'#skF_2','#skF_1',E_1985,'#skF_4') = k5_relat_1(E_1985,'#skF_4')
      | ~ m1_subset_1(E_1985,k1_zfmisc_1(k2_zfmisc_1(A_1983,B_1984)))
      | ~ v1_funct_1(E_1985) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_51900])).

tff(c_52024,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_148,c_52012])).

tff(c_52032,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_52024])).

tff(c_52377,plain,(
    ! [D_2000,B_1999,C_2002,E_2004,F_2003,A_2001] :
      ( m1_subset_1(k1_partfun1(A_2001,B_1999,C_2002,D_2000,E_2004,F_2003),k1_zfmisc_1(k2_zfmisc_1(A_2001,D_2000)))
      | ~ m1_subset_1(F_2003,k1_zfmisc_1(k2_zfmisc_1(C_2002,D_2000)))
      | ~ v1_funct_1(F_2003)
      | ~ m1_subset_1(E_2004,k1_zfmisc_1(k2_zfmisc_1(A_2001,B_1999)))
      | ~ v1_funct_1(E_2004) ) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_52444,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_52032,c_52377])).

tff(c_52475,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_148,c_146,c_142,c_52444])).

tff(c_102,plain,(
    ! [A_61] : m1_subset_1(k6_partfun1(A_61),k1_zfmisc_1(k2_zfmisc_1(A_61,A_61))) ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_138,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_362])).

tff(c_51310,plain,(
    ! [D_1942,C_1943,A_1944,B_1945] :
      ( D_1942 = C_1943
      | ~ r2_relset_1(A_1944,B_1945,C_1943,D_1942)
      | ~ m1_subset_1(D_1942,k1_zfmisc_1(k2_zfmisc_1(A_1944,B_1945)))
      | ~ m1_subset_1(C_1943,k1_zfmisc_1(k2_zfmisc_1(A_1944,B_1945))) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_51318,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_138,c_51310])).

tff(c_51333,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_51318])).

tff(c_51614,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_51333])).

tff(c_53027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52475,c_52032,c_51614])).

tff(c_53028,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_51333])).

tff(c_54343,plain,(
    ! [E_2109,B_2113,C_2111,D_2110,A_2112] :
      ( k1_xboole_0 = C_2111
      | v2_funct_1(E_2109)
      | k2_relset_1(A_2112,B_2113,D_2110) != B_2113
      | ~ v2_funct_1(k1_partfun1(A_2112,B_2113,B_2113,C_2111,D_2110,E_2109))
      | ~ m1_subset_1(E_2109,k1_zfmisc_1(k2_zfmisc_1(B_2113,C_2111)))
      | ~ v1_funct_2(E_2109,B_2113,C_2111)
      | ~ v1_funct_1(E_2109)
      | ~ m1_subset_1(D_2110,k1_zfmisc_1(k2_zfmisc_1(A_2112,B_2113)))
      | ~ v1_funct_2(D_2110,A_2112,B_2113)
      | ~ v1_funct_1(D_2110) ) ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_54347,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_53028,c_54343])).

tff(c_54352,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_150,c_148,c_146,c_144,c_142,c_155,c_140,c_54347])).

tff(c_54354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51460,c_134,c_54352])).

tff(c_54356,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_51424])).

tff(c_40,plain,(
    ! [A_24] :
      ( k4_relat_1(A_24) = k2_funct_1(A_24)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_54359,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54356,c_40])).

tff(c_54362,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_146,c_54359])).

tff(c_10,plain,(
    ! [A_6] :
      ( v1_relat_1(k4_relat_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_480,plain,(
    ! [C_126,B_127,A_128] :
      ( v5_relat_1(C_126,B_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_491,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_142,c_480])).

tff(c_741,plain,(
    ! [B_142,A_143] :
      ( k2_relat_1(B_142) = A_143
      | ~ v2_funct_2(B_142,A_143)
      | ~ v5_relat_1(B_142,A_143)
      | ~ v1_relat_1(B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_750,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_491,c_741])).

tff(c_759,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_750])).

tff(c_11069,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_759])).

tff(c_26947,plain,(
    ! [C_1012,A_1013,D_1016,E_1011,B_1014,F_1015] :
      ( k1_partfun1(A_1013,B_1014,C_1012,D_1016,E_1011,F_1015) = k5_relat_1(E_1011,F_1015)
      | ~ m1_subset_1(F_1015,k1_zfmisc_1(k2_zfmisc_1(C_1012,D_1016)))
      | ~ v1_funct_1(F_1015)
      | ~ m1_subset_1(E_1011,k1_zfmisc_1(k2_zfmisc_1(A_1013,B_1014)))
      | ~ v1_funct_1(E_1011) ) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_26951,plain,(
    ! [A_1013,B_1014,E_1011] :
      ( k1_partfun1(A_1013,B_1014,'#skF_2','#skF_1',E_1011,'#skF_4') = k5_relat_1(E_1011,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_1011,k1_zfmisc_1(k2_zfmisc_1(A_1013,B_1014)))
      | ~ v1_funct_1(E_1011) ) ),
    inference(resolution,[status(thm)],[c_142,c_26947])).

tff(c_27164,plain,(
    ! [A_1024,B_1025,E_1026] :
      ( k1_partfun1(A_1024,B_1025,'#skF_2','#skF_1',E_1026,'#skF_4') = k5_relat_1(E_1026,'#skF_4')
      | ~ m1_subset_1(E_1026,k1_zfmisc_1(k2_zfmisc_1(A_1024,B_1025)))
      | ~ v1_funct_1(E_1026) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_26951])).

tff(c_27176,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_148,c_27164])).

tff(c_27184,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_27176])).

tff(c_27265,plain,(
    r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27184,c_138])).

tff(c_27986,plain,(
    ! [D_1057,A_1058,B_1059,C_1060] :
      ( v2_funct_2(D_1057,A_1058)
      | ~ r2_relset_1(A_1058,A_1058,k1_partfun1(A_1058,B_1059,B_1059,A_1058,C_1060,D_1057),k6_partfun1(A_1058))
      | ~ m1_subset_1(D_1057,k1_zfmisc_1(k2_zfmisc_1(B_1059,A_1058)))
      | ~ v1_funct_2(D_1057,B_1059,A_1058)
      | ~ v1_funct_1(D_1057)
      | ~ m1_subset_1(C_1060,k1_zfmisc_1(k2_zfmisc_1(A_1058,B_1059)))
      | ~ v1_funct_2(C_1060,A_1058,B_1059)
      | ~ v1_funct_1(C_1060) ) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_27992,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_27184,c_27986])).

tff(c_27996,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_150,c_148,c_146,c_144,c_142,c_27265,c_27992])).

tff(c_27998,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11069,c_27996])).

tff(c_27999,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_759])).

tff(c_26,plain,(
    ! [A_16] :
      ( k1_relat_1(k4_relat_1(A_16)) = k2_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_344,plain,(
    ! [B_114,A_115] :
      ( r1_tarski(k10_relat_1(B_114,A_115),k1_relat_1(B_114))
      | ~ v1_relat_1(B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28331,plain,(
    ! [A_1078,A_1079] :
      ( r1_tarski(k10_relat_1(k4_relat_1(A_1078),A_1079),k2_relat_1(A_1078))
      | ~ v1_relat_1(k4_relat_1(A_1078))
      | ~ v1_relat_1(A_1078) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_344])).

tff(c_28339,plain,(
    ! [A_1079] :
      ( r1_tarski(k10_relat_1(k4_relat_1('#skF_4'),A_1079),'#skF_1')
      | ~ v1_relat_1(k4_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27999,c_28331])).

tff(c_28373,plain,(
    ! [A_1079] :
      ( r1_tarski(k10_relat_1(k4_relat_1('#skF_4'),A_1079),'#skF_1')
      | ~ v1_relat_1(k4_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_28339])).

tff(c_28400,plain,(
    ~ v1_relat_1(k4_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_28373])).

tff(c_28421,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_28400])).

tff(c_28425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_28421])).

tff(c_28427,plain,(
    v1_relat_1(k4_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_28373])).

tff(c_54383,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54362,c_28427])).

tff(c_42,plain,(
    ! [A_25] :
      ( v1_funct_1(k2_funct_1(A_25))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_311,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_148,c_302])).

tff(c_320,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_311])).

tff(c_136,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_362])).

tff(c_507,plain,(
    ! [A_133] :
      ( k4_relat_1(A_133) = k2_funct_1(A_133)
      | ~ v2_funct_1(A_133)
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_513,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_136,c_507])).

tff(c_519,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_152,c_513])).

tff(c_532,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_10])).

tff(c_542,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_532])).

tff(c_51418,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_148,c_51409])).

tff(c_51427,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_150,c_136,c_140,c_51418])).

tff(c_54423,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_54362,c_26])).

tff(c_54460,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_27999,c_54423])).

tff(c_34,plain,(
    ! [A_21] : k4_relat_1(k6_relat_1(A_21)) = k6_relat_1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_159,plain,(
    ! [A_21] : k4_relat_1(k6_partfun1(A_21)) = k6_partfun1(A_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_106,c_34])).

tff(c_96,plain,(
    ! [B_56,E_59,C_57,A_55,F_60,D_58] :
      ( m1_subset_1(k1_partfun1(A_55,B_56,C_57,D_58,E_59,F_60),k1_zfmisc_1(k2_zfmisc_1(A_55,D_58)))
      | ~ m1_subset_1(F_60,k1_zfmisc_1(k2_zfmisc_1(C_57,D_58)))
      | ~ v1_funct_1(F_60)
      | ~ m1_subset_1(E_59,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56)))
      | ~ v1_funct_1(E_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_54468,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_51333])).

tff(c_56229,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_54468])).

tff(c_56233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_148,c_146,c_142,c_56229])).

tff(c_56234,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_51333])).

tff(c_56774,plain,(
    ! [A_2213,C_2212,B_2214,F_2215,D_2216,E_2211] :
      ( k1_partfun1(A_2213,B_2214,C_2212,D_2216,E_2211,F_2215) = k5_relat_1(E_2211,F_2215)
      | ~ m1_subset_1(F_2215,k1_zfmisc_1(k2_zfmisc_1(C_2212,D_2216)))
      | ~ v1_funct_1(F_2215)
      | ~ m1_subset_1(E_2211,k1_zfmisc_1(k2_zfmisc_1(A_2213,B_2214)))
      | ~ v1_funct_1(E_2211) ) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_56780,plain,(
    ! [A_2213,B_2214,E_2211] :
      ( k1_partfun1(A_2213,B_2214,'#skF_2','#skF_1',E_2211,'#skF_4') = k5_relat_1(E_2211,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_2211,k1_zfmisc_1(k2_zfmisc_1(A_2213,B_2214)))
      | ~ v1_funct_1(E_2211) ) ),
    inference(resolution,[status(thm)],[c_142,c_56774])).

tff(c_56968,plain,(
    ! [A_2228,B_2229,E_2230] :
      ( k1_partfun1(A_2228,B_2229,'#skF_2','#skF_1',E_2230,'#skF_4') = k5_relat_1(E_2230,'#skF_4')
      | ~ m1_subset_1(E_2230,k1_zfmisc_1(k2_zfmisc_1(A_2228,B_2229)))
      | ~ v1_funct_1(E_2230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_56780])).

tff(c_56980,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_148,c_56968])).

tff(c_56988,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_56234,c_56980])).

tff(c_28826,plain,(
    ! [B_1093,A_1094] :
      ( k5_relat_1(k4_relat_1(B_1093),k4_relat_1(A_1094)) = k4_relat_1(k5_relat_1(A_1094,B_1093))
      | ~ v1_relat_1(B_1093)
      | ~ v1_relat_1(A_1094) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28844,plain,(
    ! [B_1093] :
      ( k5_relat_1(k4_relat_1(B_1093),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3',B_1093))
      | ~ v1_relat_1(B_1093)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_28826])).

tff(c_28866,plain,(
    ! [B_1093] :
      ( k5_relat_1(k4_relat_1(B_1093),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3',B_1093))
      | ~ v1_relat_1(B_1093) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_28844])).

tff(c_54405,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_54362,c_28866])).

tff(c_54448,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_54405])).

tff(c_57001,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_56988,c_54448])).

tff(c_54,plain,(
    ! [A_31,B_33] :
      ( v2_funct_1(A_31)
      | k6_relat_1(k1_relat_1(A_31)) != k5_relat_1(A_31,B_33)
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_154,plain,(
    ! [A_31,B_33] :
      ( v2_funct_1(A_31)
      | k6_partfun1(k1_relat_1(A_31)) != k5_relat_1(A_31,B_33)
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_54])).

tff(c_57006,plain,
    ( v2_funct_1(k2_funct_1('#skF_4'))
    | k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))) != k6_partfun1('#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_57001,c_154])).

tff(c_57015,plain,
    ( v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54383,c_542,c_51427,c_54460,c_57006])).

tff(c_57019,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_57015])).

tff(c_57022,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_57019])).

tff(c_57026,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_146,c_57022])).

tff(c_57028,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_57015])).

tff(c_57027,plain,(
    v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_57015])).

tff(c_132,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_362])).

tff(c_28099,plain,(
    ! [A_1062,B_1063,C_1064] :
      ( k1_relset_1(A_1062,B_1063,C_1064) = k1_relat_1(C_1064)
      | ~ m1_subset_1(C_1064,k1_zfmisc_1(k2_zfmisc_1(A_1062,B_1063))) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_28112,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_148,c_28099])).

tff(c_51107,plain,(
    ! [B_1939,A_1940,C_1941] :
      ( k1_xboole_0 = B_1939
      | k1_relset_1(A_1940,B_1939,C_1941) = A_1940
      | ~ v1_funct_2(C_1941,A_1940,B_1939)
      | ~ m1_subset_1(C_1941,k1_zfmisc_1(k2_zfmisc_1(A_1940,B_1939))) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_51116,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_148,c_51107])).

tff(c_51125,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_28112,c_51116])).

tff(c_51126,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_51125])).

tff(c_24,plain,(
    ! [A_16] :
      ( k2_relat_1(k4_relat_1(A_16)) = k1_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_526,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_24])).

tff(c_538,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_526])).

tff(c_51181,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51126,c_538])).

tff(c_28111,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_142,c_28099])).

tff(c_51113,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_142,c_51107])).

tff(c_51121,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_28111,c_51113])).

tff(c_51122,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_51121])).

tff(c_54426,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_54362,c_24])).

tff(c_54462,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_51122,c_54426])).

tff(c_14,plain,(
    ! [A_9] :
      ( k4_relat_1(k4_relat_1(A_9)) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_54429,plain,
    ( k4_relat_1(k2_funct_1('#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_54362,c_14])).

tff(c_54464,plain,(
    k4_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_54429])).

tff(c_57031,plain,
    ( k4_relat_1(k2_funct_1('#skF_4')) = k2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_57027,c_40])).

tff(c_57034,plain,
    ( k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4'
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54383,c_54464,c_57031])).

tff(c_57118,plain,(
    k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57028,c_57034])).

tff(c_28841,plain,(
    ! [A_1094] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k4_relat_1(A_1094)) = k4_relat_1(k5_relat_1(A_1094,'#skF_3'))
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_1094) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_28826])).

tff(c_28864,plain,(
    ! [A_1094] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k4_relat_1(A_1094)) = k4_relat_1(k5_relat_1(A_1094,'#skF_3'))
      | ~ v1_relat_1(A_1094) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_28841])).

tff(c_54408,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1('#skF_4')) = k4_relat_1(k5_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_54362,c_28864])).

tff(c_54450,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1('#skF_4')) = k4_relat_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_54408])).

tff(c_68,plain,(
    ! [A_37,B_39] :
      ( k2_funct_1(A_37) = B_39
      | k6_relat_1(k2_relat_1(A_37)) != k5_relat_1(B_39,A_37)
      | k2_relat_1(B_39) != k1_relat_1(A_37)
      | ~ v2_funct_1(A_37)
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_153,plain,(
    ! [A_37,B_39] :
      ( k2_funct_1(A_37) = B_39
      | k6_partfun1(k2_relat_1(A_37)) != k5_relat_1(B_39,A_37)
      | k2_relat_1(B_39) != k1_relat_1(A_37)
      | ~ v2_funct_1(A_37)
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_68])).

tff(c_57511,plain,
    ( k2_funct_1(k2_funct_1('#skF_4')) = k2_funct_1('#skF_3')
    | k6_partfun1(k2_relat_1(k2_funct_1('#skF_4'))) != k4_relat_1(k5_relat_1('#skF_4','#skF_3'))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_54450,c_153])).

tff(c_57520,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k4_relat_1(k5_relat_1('#skF_4','#skF_3')) != k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54383,c_57028,c_542,c_51427,c_57027,c_51181,c_54460,c_54462,c_57118,c_57511])).

tff(c_57521,plain,(
    k4_relat_1(k5_relat_1('#skF_4','#skF_3')) != k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_57520])).

tff(c_56897,plain,(
    ! [B_2223,C_2224,A_2225] :
      ( k6_partfun1(B_2223) = k5_relat_1(k2_funct_1(C_2224),C_2224)
      | k1_xboole_0 = B_2223
      | ~ v2_funct_1(C_2224)
      | k2_relset_1(A_2225,B_2223,C_2224) != B_2223
      | ~ m1_subset_1(C_2224,k1_zfmisc_1(k2_zfmisc_1(A_2225,B_2223)))
      | ~ v1_funct_2(C_2224,A_2225,B_2223)
      | ~ v1_funct_1(C_2224) ) ),
    inference(cnfTransformation,[status(thm)],[f_336])).

tff(c_56905,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_148,c_56897])).

tff(c_56916,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_150,c_140,c_136,c_56905])).

tff(c_56917,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_56916])).

tff(c_529,plain,
    ( k4_relat_1(k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_14])).

tff(c_540,plain,(
    k4_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_529])).

tff(c_120,plain,(
    ! [C_82,B_81,A_80] :
      ( m1_subset_1(k2_funct_1(C_82),k1_zfmisc_1(k2_zfmisc_1(B_81,A_80)))
      | k2_relset_1(A_80,B_81,C_82) != B_81
      | ~ v2_funct_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_2(C_82,A_80,B_81)
      | ~ v1_funct_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_320])).

tff(c_492,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_148,c_480])).

tff(c_747,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_492,c_741])).

tff(c_756,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_747])).

tff(c_760,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_756])).

tff(c_30,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_161,plain,(
    ! [A_20] : k1_relat_1(k6_partfun1(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_30])).

tff(c_10943,plain,(
    ! [B_402,C_403,A_404] :
      ( k6_partfun1(B_402) = k5_relat_1(k2_funct_1(C_403),C_403)
      | k1_xboole_0 = B_402
      | ~ v2_funct_1(C_403)
      | k2_relset_1(A_404,B_402,C_403) != B_402
      | ~ m1_subset_1(C_403,k1_zfmisc_1(k2_zfmisc_1(A_404,B_402)))
      | ~ v1_funct_2(C_403,A_404,B_402)
      | ~ v1_funct_1(C_403) ) ),
    inference(cnfTransformation,[status(thm)],[f_336])).

tff(c_10951,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_148,c_10943])).

tff(c_10962,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_150,c_140,c_136,c_10951])).

tff(c_10963,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_10962])).

tff(c_66,plain,(
    ! [A_36] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_36),A_36)) = k2_relat_1(A_36)
      | ~ v2_funct_1(A_36)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_10977,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10963,c_66])).

tff(c_10990,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_152,c_136,c_161,c_10977])).

tff(c_92,plain,(
    ! [B_54] :
      ( v2_funct_2(B_54,k2_relat_1(B_54))
      | ~ v5_relat_1(B_54,k2_relat_1(B_54))
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_11035,plain,
    ( v2_funct_2('#skF_3',k2_relat_1('#skF_3'))
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10990,c_92])).

tff(c_11064,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_492,c_10990,c_11035])).

tff(c_11066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_760,c_11064])).

tff(c_11067,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_756])).

tff(c_523,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_26])).

tff(c_536,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_523])).

tff(c_28005,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11067,c_536])).

tff(c_57004,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = k2_funct_1('#skF_4')
    | k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) != k6_partfun1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_57001,c_153])).

tff(c_57013,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = k2_funct_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_51427,c_54383,c_54462,c_28005,c_51181,c_57004])).

tff(c_66932,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = k2_funct_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57028,c_57013])).

tff(c_66933,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_66932])).

tff(c_56636,plain,(
    ! [C_2204,B_2205,A_2206] :
      ( v1_funct_2(k2_funct_1(C_2204),B_2205,A_2206)
      | k2_relset_1(A_2206,B_2205,C_2204) != B_2205
      | ~ v2_funct_1(C_2204)
      | ~ m1_subset_1(C_2204,k1_zfmisc_1(k2_zfmisc_1(A_2206,B_2205)))
      | ~ v1_funct_2(C_2204,A_2206,B_2205)
      | ~ v1_funct_1(C_2204) ) ),
    inference(cnfTransformation,[status(thm)],[f_320])).

tff(c_56645,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_148,c_56636])).

tff(c_56654,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_150,c_136,c_140,c_56645])).

tff(c_731,plain,(
    ! [A_139,B_140,D_141] :
      ( r2_relset_1(A_139,B_140,D_141,D_141)
      | ~ m1_subset_1(D_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_738,plain,(
    ! [A_61] : r2_relset_1(A_61,A_61,k6_partfun1(A_61),k6_partfun1(A_61)) ),
    inference(resolution,[status(thm)],[c_102,c_731])).

tff(c_56782,plain,(
    ! [A_2213,B_2214,E_2211] :
      ( k1_partfun1(A_2213,B_2214,'#skF_1','#skF_2',E_2211,'#skF_3') = k5_relat_1(E_2211,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_2211,k1_zfmisc_1(k2_zfmisc_1(A_2213,B_2214)))
      | ~ v1_funct_1(E_2211) ) ),
    inference(resolution,[status(thm)],[c_148,c_56774])).

tff(c_65504,plain,(
    ! [A_2345,B_2346,E_2347] :
      ( k1_partfun1(A_2345,B_2346,'#skF_1','#skF_2',E_2347,'#skF_3') = k5_relat_1(E_2347,'#skF_3')
      | ~ m1_subset_1(E_2347,k1_zfmisc_1(k2_zfmisc_1(A_2345,B_2346)))
      | ~ v1_funct_1(E_2347) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_56782])).

tff(c_75479,plain,(
    ! [B_2419,A_2420,C_2421] :
      ( k1_partfun1(B_2419,A_2420,'#skF_1','#skF_2',k2_funct_1(C_2421),'#skF_3') = k5_relat_1(k2_funct_1(C_2421),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(C_2421))
      | k2_relset_1(A_2420,B_2419,C_2421) != B_2419
      | ~ v2_funct_1(C_2421)
      | ~ m1_subset_1(C_2421,k1_zfmisc_1(k2_zfmisc_1(A_2420,B_2419)))
      | ~ v1_funct_2(C_2421,A_2420,B_2419)
      | ~ v1_funct_1(C_2421) ) ),
    inference(resolution,[status(thm)],[c_120,c_65504])).

tff(c_75509,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_148,c_75479])).

tff(c_75535,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_150,c_136,c_140,c_51427,c_56917,c_75509])).

tff(c_110,plain,(
    ! [C_71,A_69,B_70,D_73] :
      ( v2_funct_1(C_71)
      | ~ r2_relset_1(A_69,A_69,k1_partfun1(A_69,B_70,B_70,A_69,C_71,D_73),k6_partfun1(A_69))
      | ~ m1_subset_1(D_73,k1_zfmisc_1(k2_zfmisc_1(B_70,A_69)))
      | ~ v1_funct_2(D_73,B_70,A_69)
      | ~ v1_funct_1(D_73)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ v1_funct_2(C_71,A_69,B_70)
      | ~ v1_funct_1(C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_75548,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_75535,c_110])).

tff(c_75563,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51427,c_56654,c_152,c_150,c_148,c_738,c_75548])).

tff(c_75564,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_66933,c_75563])).

tff(c_75570,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_75564])).

tff(c_75574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_150,c_148,c_136,c_140,c_75570])).

tff(c_75576,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_66932])).

tff(c_75579,plain,
    ( k4_relat_1(k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_75576,c_40])).

tff(c_75582,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_51427,c_540,c_75579])).

tff(c_75575,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = k2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_66932])).

tff(c_75642,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75582,c_75575])).

tff(c_75655,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k4_relat_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75642,c_54450])).

tff(c_75679,plain,(
    k4_relat_1(k5_relat_1('#skF_4','#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56917,c_75655])).

tff(c_75681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57521,c_75679])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.29  % Computer   : n020.cluster.edu
% 0.10/0.29  % Model      : x86_64 x86_64
% 0.10/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.29  % Memory     : 8042.1875MB
% 0.10/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.29  % CPULimit   : 60
% 0.10/0.29  % DateTime   : Tue Dec  1 18:20:52 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.69/13.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.69/13.85  
% 22.69/13.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.69/13.85  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 22.69/13.85  
% 22.69/13.85  %Foreground sorts:
% 22.69/13.85  
% 22.69/13.85  
% 22.69/13.85  %Background operators:
% 22.69/13.85  
% 22.69/13.85  
% 22.69/13.85  %Foreground operators:
% 22.69/13.85  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 22.69/13.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 22.69/13.85  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 22.69/13.85  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 22.69/13.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.69/13.85  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 22.69/13.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.69/13.85  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 22.69/13.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.69/13.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 22.69/13.85  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 22.69/13.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 22.69/13.85  tff('#skF_2', type, '#skF_2': $i).
% 22.69/13.85  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 22.69/13.85  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 22.69/13.85  tff('#skF_3', type, '#skF_3': $i).
% 22.69/13.85  tff('#skF_1', type, '#skF_1': $i).
% 22.69/13.85  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 22.69/13.85  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 22.69/13.85  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 22.69/13.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.69/13.85  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 22.69/13.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.69/13.85  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 22.69/13.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 22.69/13.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 22.69/13.85  tff('#skF_4', type, '#skF_4': $i).
% 22.69/13.85  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 22.69/13.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.69/13.85  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 22.69/13.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 22.69/13.85  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 22.69/13.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.69/13.85  
% 22.69/13.89  tff(f_362, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 22.69/13.89  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 22.69/13.89  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 22.69/13.89  tff(f_320, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 22.69/13.89  tff(f_259, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 22.69/13.89  tff(f_111, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 22.69/13.89  tff(f_257, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 22.69/13.89  tff(f_243, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 22.69/13.89  tff(f_247, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 22.69/13.89  tff(f_205, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 22.69/13.89  tff(f_304, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 22.69/13.89  tff(f_99, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 22.69/13.89  tff(f_42, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 22.69/13.89  tff(f_193, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 22.69/13.89  tff(f_231, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 22.69/13.89  tff(f_278, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 22.69/13.89  tff(f_70, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 22.69/13.89  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 22.69/13.89  tff(f_107, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 22.69/13.89  tff(f_83, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 22.69/13.89  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 22.69/13.89  tff(f_140, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_funct_1)).
% 22.69/13.89  tff(f_197, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 22.69/13.89  tff(f_223, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 22.69/13.89  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 22.69/13.89  tff(f_187, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 22.69/13.89  tff(f_336, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 22.69/13.89  tff(f_81, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 22.69/13.89  tff(f_170, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 22.69/13.89  tff(c_130, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_362])).
% 22.69/13.89  tff(c_12, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 22.69/13.89  tff(c_142, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_362])).
% 22.69/13.89  tff(c_302, plain, (![B_106, A_107]: (v1_relat_1(B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(A_107)) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_38])).
% 22.69/13.89  tff(c_308, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_142, c_302])).
% 22.69/13.89  tff(c_317, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_308])).
% 22.69/13.89  tff(c_146, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_362])).
% 22.69/13.89  tff(c_144, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_362])).
% 22.69/13.89  tff(c_51409, plain, (![C_1948, A_1949, B_1950]: (v1_funct_1(k2_funct_1(C_1948)) | k2_relset_1(A_1949, B_1950, C_1948)!=B_1950 | ~v2_funct_1(C_1948) | ~m1_subset_1(C_1948, k1_zfmisc_1(k2_zfmisc_1(A_1949, B_1950))) | ~v1_funct_2(C_1948, A_1949, B_1950) | ~v1_funct_1(C_1948))), inference(cnfTransformation, [status(thm)], [f_320])).
% 22.69/13.89  tff(c_51415, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_142, c_51409])).
% 22.69/13.89  tff(c_51424, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_144, c_51415])).
% 22.69/13.89  tff(c_51460, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_51424])).
% 22.69/13.89  tff(c_134, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_362])).
% 22.69/13.89  tff(c_152, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_362])).
% 22.69/13.89  tff(c_150, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_362])).
% 22.69/13.89  tff(c_148, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_362])).
% 22.69/13.89  tff(c_106, plain, (![A_68]: (k6_relat_1(A_68)=k6_partfun1(A_68))), inference(cnfTransformation, [status(thm)], [f_259])).
% 22.69/13.89  tff(c_48, plain, (![A_26]: (v2_funct_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 22.69/13.89  tff(c_155, plain, (![A_26]: (v2_funct_1(k6_partfun1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_48])).
% 22.69/13.89  tff(c_140, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_362])).
% 22.69/13.89  tff(c_51894, plain, (![A_1977, E_1975, B_1978, C_1976, D_1980, F_1979]: (k1_partfun1(A_1977, B_1978, C_1976, D_1980, E_1975, F_1979)=k5_relat_1(E_1975, F_1979) | ~m1_subset_1(F_1979, k1_zfmisc_1(k2_zfmisc_1(C_1976, D_1980))) | ~v1_funct_1(F_1979) | ~m1_subset_1(E_1975, k1_zfmisc_1(k2_zfmisc_1(A_1977, B_1978))) | ~v1_funct_1(E_1975))), inference(cnfTransformation, [status(thm)], [f_257])).
% 22.69/13.89  tff(c_51900, plain, (![A_1977, B_1978, E_1975]: (k1_partfun1(A_1977, B_1978, '#skF_2', '#skF_1', E_1975, '#skF_4')=k5_relat_1(E_1975, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_1975, k1_zfmisc_1(k2_zfmisc_1(A_1977, B_1978))) | ~v1_funct_1(E_1975))), inference(resolution, [status(thm)], [c_142, c_51894])).
% 22.69/13.89  tff(c_52012, plain, (![A_1983, B_1984, E_1985]: (k1_partfun1(A_1983, B_1984, '#skF_2', '#skF_1', E_1985, '#skF_4')=k5_relat_1(E_1985, '#skF_4') | ~m1_subset_1(E_1985, k1_zfmisc_1(k2_zfmisc_1(A_1983, B_1984))) | ~v1_funct_1(E_1985))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_51900])).
% 22.69/13.89  tff(c_52024, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_148, c_52012])).
% 22.69/13.89  tff(c_52032, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_52024])).
% 22.69/13.89  tff(c_52377, plain, (![D_2000, B_1999, C_2002, E_2004, F_2003, A_2001]: (m1_subset_1(k1_partfun1(A_2001, B_1999, C_2002, D_2000, E_2004, F_2003), k1_zfmisc_1(k2_zfmisc_1(A_2001, D_2000))) | ~m1_subset_1(F_2003, k1_zfmisc_1(k2_zfmisc_1(C_2002, D_2000))) | ~v1_funct_1(F_2003) | ~m1_subset_1(E_2004, k1_zfmisc_1(k2_zfmisc_1(A_2001, B_1999))) | ~v1_funct_1(E_2004))), inference(cnfTransformation, [status(thm)], [f_243])).
% 22.69/13.89  tff(c_52444, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_52032, c_52377])).
% 22.69/13.89  tff(c_52475, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_148, c_146, c_142, c_52444])).
% 22.69/13.89  tff(c_102, plain, (![A_61]: (m1_subset_1(k6_partfun1(A_61), k1_zfmisc_1(k2_zfmisc_1(A_61, A_61))))), inference(cnfTransformation, [status(thm)], [f_247])).
% 22.69/13.89  tff(c_138, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_362])).
% 22.69/13.89  tff(c_51310, plain, (![D_1942, C_1943, A_1944, B_1945]: (D_1942=C_1943 | ~r2_relset_1(A_1944, B_1945, C_1943, D_1942) | ~m1_subset_1(D_1942, k1_zfmisc_1(k2_zfmisc_1(A_1944, B_1945))) | ~m1_subset_1(C_1943, k1_zfmisc_1(k2_zfmisc_1(A_1944, B_1945))))), inference(cnfTransformation, [status(thm)], [f_205])).
% 22.69/13.89  tff(c_51318, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_138, c_51310])).
% 22.69/13.89  tff(c_51333, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_51318])).
% 22.69/13.89  tff(c_51614, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_51333])).
% 22.69/13.89  tff(c_53027, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52475, c_52032, c_51614])).
% 22.69/13.89  tff(c_53028, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_51333])).
% 22.69/13.89  tff(c_54343, plain, (![E_2109, B_2113, C_2111, D_2110, A_2112]: (k1_xboole_0=C_2111 | v2_funct_1(E_2109) | k2_relset_1(A_2112, B_2113, D_2110)!=B_2113 | ~v2_funct_1(k1_partfun1(A_2112, B_2113, B_2113, C_2111, D_2110, E_2109)) | ~m1_subset_1(E_2109, k1_zfmisc_1(k2_zfmisc_1(B_2113, C_2111))) | ~v1_funct_2(E_2109, B_2113, C_2111) | ~v1_funct_1(E_2109) | ~m1_subset_1(D_2110, k1_zfmisc_1(k2_zfmisc_1(A_2112, B_2113))) | ~v1_funct_2(D_2110, A_2112, B_2113) | ~v1_funct_1(D_2110))), inference(cnfTransformation, [status(thm)], [f_304])).
% 22.69/13.89  tff(c_54347, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_53028, c_54343])).
% 22.69/13.89  tff(c_54352, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_150, c_148, c_146, c_144, c_142, c_155, c_140, c_54347])).
% 22.69/13.89  tff(c_54354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51460, c_134, c_54352])).
% 22.69/13.89  tff(c_54356, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_51424])).
% 22.69/13.89  tff(c_40, plain, (![A_24]: (k4_relat_1(A_24)=k2_funct_1(A_24) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_99])).
% 22.69/13.89  tff(c_54359, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54356, c_40])).
% 22.69/13.89  tff(c_54362, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_317, c_146, c_54359])).
% 22.69/13.89  tff(c_10, plain, (![A_6]: (v1_relat_1(k4_relat_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 22.69/13.89  tff(c_480, plain, (![C_126, B_127, A_128]: (v5_relat_1(C_126, B_127) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))))), inference(cnfTransformation, [status(thm)], [f_193])).
% 22.69/13.89  tff(c_491, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_142, c_480])).
% 22.69/13.89  tff(c_741, plain, (![B_142, A_143]: (k2_relat_1(B_142)=A_143 | ~v2_funct_2(B_142, A_143) | ~v5_relat_1(B_142, A_143) | ~v1_relat_1(B_142))), inference(cnfTransformation, [status(thm)], [f_231])).
% 22.69/13.89  tff(c_750, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_491, c_741])).
% 22.69/13.89  tff(c_759, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_317, c_750])).
% 22.69/13.89  tff(c_11069, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_759])).
% 22.69/13.89  tff(c_26947, plain, (![C_1012, A_1013, D_1016, E_1011, B_1014, F_1015]: (k1_partfun1(A_1013, B_1014, C_1012, D_1016, E_1011, F_1015)=k5_relat_1(E_1011, F_1015) | ~m1_subset_1(F_1015, k1_zfmisc_1(k2_zfmisc_1(C_1012, D_1016))) | ~v1_funct_1(F_1015) | ~m1_subset_1(E_1011, k1_zfmisc_1(k2_zfmisc_1(A_1013, B_1014))) | ~v1_funct_1(E_1011))), inference(cnfTransformation, [status(thm)], [f_257])).
% 22.69/13.89  tff(c_26951, plain, (![A_1013, B_1014, E_1011]: (k1_partfun1(A_1013, B_1014, '#skF_2', '#skF_1', E_1011, '#skF_4')=k5_relat_1(E_1011, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_1011, k1_zfmisc_1(k2_zfmisc_1(A_1013, B_1014))) | ~v1_funct_1(E_1011))), inference(resolution, [status(thm)], [c_142, c_26947])).
% 22.69/13.89  tff(c_27164, plain, (![A_1024, B_1025, E_1026]: (k1_partfun1(A_1024, B_1025, '#skF_2', '#skF_1', E_1026, '#skF_4')=k5_relat_1(E_1026, '#skF_4') | ~m1_subset_1(E_1026, k1_zfmisc_1(k2_zfmisc_1(A_1024, B_1025))) | ~v1_funct_1(E_1026))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_26951])).
% 22.69/13.89  tff(c_27176, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_148, c_27164])).
% 22.69/13.89  tff(c_27184, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_27176])).
% 22.69/13.89  tff(c_27265, plain, (r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_27184, c_138])).
% 22.69/13.89  tff(c_27986, plain, (![D_1057, A_1058, B_1059, C_1060]: (v2_funct_2(D_1057, A_1058) | ~r2_relset_1(A_1058, A_1058, k1_partfun1(A_1058, B_1059, B_1059, A_1058, C_1060, D_1057), k6_partfun1(A_1058)) | ~m1_subset_1(D_1057, k1_zfmisc_1(k2_zfmisc_1(B_1059, A_1058))) | ~v1_funct_2(D_1057, B_1059, A_1058) | ~v1_funct_1(D_1057) | ~m1_subset_1(C_1060, k1_zfmisc_1(k2_zfmisc_1(A_1058, B_1059))) | ~v1_funct_2(C_1060, A_1058, B_1059) | ~v1_funct_1(C_1060))), inference(cnfTransformation, [status(thm)], [f_278])).
% 22.69/13.89  tff(c_27992, plain, (v2_funct_2('#skF_4', '#skF_1') | ~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_27184, c_27986])).
% 22.69/13.89  tff(c_27996, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_150, c_148, c_146, c_144, c_142, c_27265, c_27992])).
% 22.69/13.89  tff(c_27998, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11069, c_27996])).
% 22.69/13.89  tff(c_27999, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_759])).
% 22.69/13.89  tff(c_26, plain, (![A_16]: (k1_relat_1(k4_relat_1(A_16))=k2_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 22.69/13.89  tff(c_344, plain, (![B_114, A_115]: (r1_tarski(k10_relat_1(B_114, A_115), k1_relat_1(B_114)) | ~v1_relat_1(B_114))), inference(cnfTransformation, [status(thm)], [f_60])).
% 22.69/13.89  tff(c_28331, plain, (![A_1078, A_1079]: (r1_tarski(k10_relat_1(k4_relat_1(A_1078), A_1079), k2_relat_1(A_1078)) | ~v1_relat_1(k4_relat_1(A_1078)) | ~v1_relat_1(A_1078))), inference(superposition, [status(thm), theory('equality')], [c_26, c_344])).
% 22.69/13.89  tff(c_28339, plain, (![A_1079]: (r1_tarski(k10_relat_1(k4_relat_1('#skF_4'), A_1079), '#skF_1') | ~v1_relat_1(k4_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_27999, c_28331])).
% 22.69/13.89  tff(c_28373, plain, (![A_1079]: (r1_tarski(k10_relat_1(k4_relat_1('#skF_4'), A_1079), '#skF_1') | ~v1_relat_1(k4_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_28339])).
% 22.69/13.89  tff(c_28400, plain, (~v1_relat_1(k4_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_28373])).
% 22.69/13.89  tff(c_28421, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_28400])).
% 22.69/13.89  tff(c_28425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_317, c_28421])).
% 22.69/13.89  tff(c_28427, plain, (v1_relat_1(k4_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_28373])).
% 22.69/13.89  tff(c_54383, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54362, c_28427])).
% 22.69/13.89  tff(c_42, plain, (![A_25]: (v1_funct_1(k2_funct_1(A_25)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_107])).
% 22.69/13.89  tff(c_311, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_148, c_302])).
% 22.69/13.89  tff(c_320, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_311])).
% 22.69/13.89  tff(c_136, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_362])).
% 22.69/13.89  tff(c_507, plain, (![A_133]: (k4_relat_1(A_133)=k2_funct_1(A_133) | ~v2_funct_1(A_133) | ~v1_funct_1(A_133) | ~v1_relat_1(A_133))), inference(cnfTransformation, [status(thm)], [f_99])).
% 22.69/13.89  tff(c_513, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_136, c_507])).
% 22.69/13.89  tff(c_519, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_320, c_152, c_513])).
% 22.69/13.89  tff(c_532, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_519, c_10])).
% 22.69/13.89  tff(c_542, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_532])).
% 22.69/13.89  tff(c_51418, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_148, c_51409])).
% 22.69/13.89  tff(c_51427, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_150, c_136, c_140, c_51418])).
% 22.69/13.89  tff(c_54423, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_54362, c_26])).
% 22.69/13.89  tff(c_54460, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_317, c_27999, c_54423])).
% 22.69/13.89  tff(c_34, plain, (![A_21]: (k4_relat_1(k6_relat_1(A_21))=k6_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_83])).
% 22.69/13.89  tff(c_159, plain, (![A_21]: (k4_relat_1(k6_partfun1(A_21))=k6_partfun1(A_21))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_106, c_34])).
% 22.69/13.89  tff(c_96, plain, (![B_56, E_59, C_57, A_55, F_60, D_58]: (m1_subset_1(k1_partfun1(A_55, B_56, C_57, D_58, E_59, F_60), k1_zfmisc_1(k2_zfmisc_1(A_55, D_58))) | ~m1_subset_1(F_60, k1_zfmisc_1(k2_zfmisc_1(C_57, D_58))) | ~v1_funct_1(F_60) | ~m1_subset_1(E_59, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))) | ~v1_funct_1(E_59))), inference(cnfTransformation, [status(thm)], [f_243])).
% 22.69/13.89  tff(c_54468, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_51333])).
% 22.69/13.89  tff(c_56229, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_54468])).
% 22.69/13.89  tff(c_56233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_148, c_146, c_142, c_56229])).
% 22.69/13.89  tff(c_56234, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_51333])).
% 22.69/13.89  tff(c_56774, plain, (![A_2213, C_2212, B_2214, F_2215, D_2216, E_2211]: (k1_partfun1(A_2213, B_2214, C_2212, D_2216, E_2211, F_2215)=k5_relat_1(E_2211, F_2215) | ~m1_subset_1(F_2215, k1_zfmisc_1(k2_zfmisc_1(C_2212, D_2216))) | ~v1_funct_1(F_2215) | ~m1_subset_1(E_2211, k1_zfmisc_1(k2_zfmisc_1(A_2213, B_2214))) | ~v1_funct_1(E_2211))), inference(cnfTransformation, [status(thm)], [f_257])).
% 22.69/13.89  tff(c_56780, plain, (![A_2213, B_2214, E_2211]: (k1_partfun1(A_2213, B_2214, '#skF_2', '#skF_1', E_2211, '#skF_4')=k5_relat_1(E_2211, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_2211, k1_zfmisc_1(k2_zfmisc_1(A_2213, B_2214))) | ~v1_funct_1(E_2211))), inference(resolution, [status(thm)], [c_142, c_56774])).
% 22.69/13.89  tff(c_56968, plain, (![A_2228, B_2229, E_2230]: (k1_partfun1(A_2228, B_2229, '#skF_2', '#skF_1', E_2230, '#skF_4')=k5_relat_1(E_2230, '#skF_4') | ~m1_subset_1(E_2230, k1_zfmisc_1(k2_zfmisc_1(A_2228, B_2229))) | ~v1_funct_1(E_2230))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_56780])).
% 22.69/13.89  tff(c_56980, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_148, c_56968])).
% 22.69/13.89  tff(c_56988, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_56234, c_56980])).
% 22.69/13.89  tff(c_28826, plain, (![B_1093, A_1094]: (k5_relat_1(k4_relat_1(B_1093), k4_relat_1(A_1094))=k4_relat_1(k5_relat_1(A_1094, B_1093)) | ~v1_relat_1(B_1093) | ~v1_relat_1(A_1094))), inference(cnfTransformation, [status(thm)], [f_77])).
% 22.69/13.89  tff(c_28844, plain, (![B_1093]: (k5_relat_1(k4_relat_1(B_1093), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', B_1093)) | ~v1_relat_1(B_1093) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_519, c_28826])).
% 22.69/13.89  tff(c_28866, plain, (![B_1093]: (k5_relat_1(k4_relat_1(B_1093), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', B_1093)) | ~v1_relat_1(B_1093))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_28844])).
% 22.69/13.89  tff(c_54405, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_54362, c_28866])).
% 22.69/13.89  tff(c_54448, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_54405])).
% 22.69/13.89  tff(c_57001, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_56988, c_54448])).
% 22.69/13.89  tff(c_54, plain, (![A_31, B_33]: (v2_funct_1(A_31) | k6_relat_1(k1_relat_1(A_31))!=k5_relat_1(A_31, B_33) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_140])).
% 22.69/13.89  tff(c_154, plain, (![A_31, B_33]: (v2_funct_1(A_31) | k6_partfun1(k1_relat_1(A_31))!=k5_relat_1(A_31, B_33) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_54])).
% 22.69/13.89  tff(c_57006, plain, (v2_funct_1(k2_funct_1('#skF_4')) | k6_partfun1(k1_relat_1(k2_funct_1('#skF_4')))!=k6_partfun1('#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_57001, c_154])).
% 22.69/13.89  tff(c_57015, plain, (v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54383, c_542, c_51427, c_54460, c_57006])).
% 22.69/13.89  tff(c_57019, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_57015])).
% 22.69/13.89  tff(c_57022, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_57019])).
% 22.69/13.89  tff(c_57026, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_317, c_146, c_57022])).
% 22.69/13.89  tff(c_57028, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_57015])).
% 22.69/13.89  tff(c_57027, plain, (v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_57015])).
% 22.69/13.89  tff(c_132, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_362])).
% 22.69/13.89  tff(c_28099, plain, (![A_1062, B_1063, C_1064]: (k1_relset_1(A_1062, B_1063, C_1064)=k1_relat_1(C_1064) | ~m1_subset_1(C_1064, k1_zfmisc_1(k2_zfmisc_1(A_1062, B_1063))))), inference(cnfTransformation, [status(thm)], [f_197])).
% 22.69/13.89  tff(c_28112, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_148, c_28099])).
% 22.69/13.89  tff(c_51107, plain, (![B_1939, A_1940, C_1941]: (k1_xboole_0=B_1939 | k1_relset_1(A_1940, B_1939, C_1941)=A_1940 | ~v1_funct_2(C_1941, A_1940, B_1939) | ~m1_subset_1(C_1941, k1_zfmisc_1(k2_zfmisc_1(A_1940, B_1939))))), inference(cnfTransformation, [status(thm)], [f_223])).
% 22.69/13.89  tff(c_51116, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_148, c_51107])).
% 22.69/13.89  tff(c_51125, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_28112, c_51116])).
% 22.69/13.89  tff(c_51126, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_132, c_51125])).
% 22.69/13.89  tff(c_24, plain, (![A_16]: (k2_relat_1(k4_relat_1(A_16))=k1_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 22.69/13.89  tff(c_526, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_519, c_24])).
% 22.69/13.89  tff(c_538, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_320, c_526])).
% 22.69/13.89  tff(c_51181, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_51126, c_538])).
% 22.69/13.89  tff(c_28111, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_142, c_28099])).
% 22.69/13.89  tff(c_51113, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_142, c_51107])).
% 22.69/13.89  tff(c_51121, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_28111, c_51113])).
% 22.69/13.89  tff(c_51122, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_134, c_51121])).
% 22.69/13.89  tff(c_54426, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_54362, c_24])).
% 22.69/13.89  tff(c_54462, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_317, c_51122, c_54426])).
% 22.69/13.89  tff(c_14, plain, (![A_9]: (k4_relat_1(k4_relat_1(A_9))=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 22.69/13.89  tff(c_54429, plain, (k4_relat_1(k2_funct_1('#skF_4'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_54362, c_14])).
% 22.69/13.89  tff(c_54464, plain, (k4_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_317, c_54429])).
% 22.69/13.89  tff(c_57031, plain, (k4_relat_1(k2_funct_1('#skF_4'))=k2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_57027, c_40])).
% 22.69/13.89  tff(c_57034, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4' | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54383, c_54464, c_57031])).
% 22.69/13.89  tff(c_57118, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_57028, c_57034])).
% 22.69/13.89  tff(c_28841, plain, (![A_1094]: (k5_relat_1(k2_funct_1('#skF_3'), k4_relat_1(A_1094))=k4_relat_1(k5_relat_1(A_1094, '#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_1094))), inference(superposition, [status(thm), theory('equality')], [c_519, c_28826])).
% 22.69/13.89  tff(c_28864, plain, (![A_1094]: (k5_relat_1(k2_funct_1('#skF_3'), k4_relat_1(A_1094))=k4_relat_1(k5_relat_1(A_1094, '#skF_3')) | ~v1_relat_1(A_1094))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_28841])).
% 22.69/13.89  tff(c_54408, plain, (k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1('#skF_4'))=k4_relat_1(k5_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_54362, c_28864])).
% 22.69/13.89  tff(c_54450, plain, (k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1('#skF_4'))=k4_relat_1(k5_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_54408])).
% 22.69/13.89  tff(c_68, plain, (![A_37, B_39]: (k2_funct_1(A_37)=B_39 | k6_relat_1(k2_relat_1(A_37))!=k5_relat_1(B_39, A_37) | k2_relat_1(B_39)!=k1_relat_1(A_37) | ~v2_funct_1(A_37) | ~v1_funct_1(B_39) | ~v1_relat_1(B_39) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_187])).
% 22.69/13.89  tff(c_153, plain, (![A_37, B_39]: (k2_funct_1(A_37)=B_39 | k6_partfun1(k2_relat_1(A_37))!=k5_relat_1(B_39, A_37) | k2_relat_1(B_39)!=k1_relat_1(A_37) | ~v2_funct_1(A_37) | ~v1_funct_1(B_39) | ~v1_relat_1(B_39) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_68])).
% 22.69/13.89  tff(c_57511, plain, (k2_funct_1(k2_funct_1('#skF_4'))=k2_funct_1('#skF_3') | k6_partfun1(k2_relat_1(k2_funct_1('#skF_4')))!=k4_relat_1(k5_relat_1('#skF_4', '#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_54450, c_153])).
% 22.69/13.89  tff(c_57520, plain, (k2_funct_1('#skF_3')='#skF_4' | k4_relat_1(k5_relat_1('#skF_4', '#skF_3'))!=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54383, c_57028, c_542, c_51427, c_57027, c_51181, c_54460, c_54462, c_57118, c_57511])).
% 22.69/13.89  tff(c_57521, plain, (k4_relat_1(k5_relat_1('#skF_4', '#skF_3'))!=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_130, c_57520])).
% 22.69/13.89  tff(c_56897, plain, (![B_2223, C_2224, A_2225]: (k6_partfun1(B_2223)=k5_relat_1(k2_funct_1(C_2224), C_2224) | k1_xboole_0=B_2223 | ~v2_funct_1(C_2224) | k2_relset_1(A_2225, B_2223, C_2224)!=B_2223 | ~m1_subset_1(C_2224, k1_zfmisc_1(k2_zfmisc_1(A_2225, B_2223))) | ~v1_funct_2(C_2224, A_2225, B_2223) | ~v1_funct_1(C_2224))), inference(cnfTransformation, [status(thm)], [f_336])).
% 22.69/13.89  tff(c_56905, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_148, c_56897])).
% 22.69/13.89  tff(c_56916, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_150, c_140, c_136, c_56905])).
% 22.69/13.89  tff(c_56917, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_132, c_56916])).
% 22.69/13.89  tff(c_529, plain, (k4_relat_1(k2_funct_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_519, c_14])).
% 22.69/13.89  tff(c_540, plain, (k4_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_320, c_529])).
% 22.69/13.89  tff(c_120, plain, (![C_82, B_81, A_80]: (m1_subset_1(k2_funct_1(C_82), k1_zfmisc_1(k2_zfmisc_1(B_81, A_80))) | k2_relset_1(A_80, B_81, C_82)!=B_81 | ~v2_funct_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_2(C_82, A_80, B_81) | ~v1_funct_1(C_82))), inference(cnfTransformation, [status(thm)], [f_320])).
% 22.69/13.89  tff(c_492, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_148, c_480])).
% 22.69/13.89  tff(c_747, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_492, c_741])).
% 22.69/13.89  tff(c_756, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_320, c_747])).
% 22.69/13.89  tff(c_760, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_756])).
% 22.69/13.89  tff(c_30, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_81])).
% 22.69/13.89  tff(c_161, plain, (![A_20]: (k1_relat_1(k6_partfun1(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_30])).
% 22.69/13.89  tff(c_10943, plain, (![B_402, C_403, A_404]: (k6_partfun1(B_402)=k5_relat_1(k2_funct_1(C_403), C_403) | k1_xboole_0=B_402 | ~v2_funct_1(C_403) | k2_relset_1(A_404, B_402, C_403)!=B_402 | ~m1_subset_1(C_403, k1_zfmisc_1(k2_zfmisc_1(A_404, B_402))) | ~v1_funct_2(C_403, A_404, B_402) | ~v1_funct_1(C_403))), inference(cnfTransformation, [status(thm)], [f_336])).
% 22.69/13.89  tff(c_10951, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_148, c_10943])).
% 22.69/13.89  tff(c_10962, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_150, c_140, c_136, c_10951])).
% 22.69/13.89  tff(c_10963, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_132, c_10962])).
% 22.69/13.89  tff(c_66, plain, (![A_36]: (k1_relat_1(k5_relat_1(k2_funct_1(A_36), A_36))=k2_relat_1(A_36) | ~v2_funct_1(A_36) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_170])).
% 22.69/13.89  tff(c_10977, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10963, c_66])).
% 22.69/13.89  tff(c_10990, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_320, c_152, c_136, c_161, c_10977])).
% 22.69/13.89  tff(c_92, plain, (![B_54]: (v2_funct_2(B_54, k2_relat_1(B_54)) | ~v5_relat_1(B_54, k2_relat_1(B_54)) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_231])).
% 22.69/13.89  tff(c_11035, plain, (v2_funct_2('#skF_3', k2_relat_1('#skF_3')) | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10990, c_92])).
% 22.69/13.89  tff(c_11064, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_320, c_492, c_10990, c_11035])).
% 22.69/13.89  tff(c_11066, plain, $false, inference(negUnitSimplification, [status(thm)], [c_760, c_11064])).
% 22.69/13.89  tff(c_11067, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_756])).
% 22.69/13.89  tff(c_523, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_519, c_26])).
% 22.69/13.89  tff(c_536, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_320, c_523])).
% 22.69/13.89  tff(c_28005, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11067, c_536])).
% 22.69/13.89  tff(c_57004, plain, (k2_funct_1(k2_funct_1('#skF_3'))=k2_funct_1('#skF_4') | k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))!=k6_partfun1('#skF_1') | k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_57001, c_153])).
% 22.69/13.89  tff(c_57013, plain, (k2_funct_1(k2_funct_1('#skF_3'))=k2_funct_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_542, c_51427, c_54383, c_54462, c_28005, c_51181, c_57004])).
% 22.69/13.89  tff(c_66932, plain, (k2_funct_1(k2_funct_1('#skF_3'))=k2_funct_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_57028, c_57013])).
% 22.69/13.89  tff(c_66933, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_66932])).
% 22.69/13.89  tff(c_56636, plain, (![C_2204, B_2205, A_2206]: (v1_funct_2(k2_funct_1(C_2204), B_2205, A_2206) | k2_relset_1(A_2206, B_2205, C_2204)!=B_2205 | ~v2_funct_1(C_2204) | ~m1_subset_1(C_2204, k1_zfmisc_1(k2_zfmisc_1(A_2206, B_2205))) | ~v1_funct_2(C_2204, A_2206, B_2205) | ~v1_funct_1(C_2204))), inference(cnfTransformation, [status(thm)], [f_320])).
% 22.69/13.89  tff(c_56645, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_148, c_56636])).
% 22.69/13.89  tff(c_56654, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_150, c_136, c_140, c_56645])).
% 22.69/13.89  tff(c_731, plain, (![A_139, B_140, D_141]: (r2_relset_1(A_139, B_140, D_141, D_141) | ~m1_subset_1(D_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_205])).
% 22.69/13.89  tff(c_738, plain, (![A_61]: (r2_relset_1(A_61, A_61, k6_partfun1(A_61), k6_partfun1(A_61)))), inference(resolution, [status(thm)], [c_102, c_731])).
% 22.69/13.89  tff(c_56782, plain, (![A_2213, B_2214, E_2211]: (k1_partfun1(A_2213, B_2214, '#skF_1', '#skF_2', E_2211, '#skF_3')=k5_relat_1(E_2211, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_2211, k1_zfmisc_1(k2_zfmisc_1(A_2213, B_2214))) | ~v1_funct_1(E_2211))), inference(resolution, [status(thm)], [c_148, c_56774])).
% 22.69/13.89  tff(c_65504, plain, (![A_2345, B_2346, E_2347]: (k1_partfun1(A_2345, B_2346, '#skF_1', '#skF_2', E_2347, '#skF_3')=k5_relat_1(E_2347, '#skF_3') | ~m1_subset_1(E_2347, k1_zfmisc_1(k2_zfmisc_1(A_2345, B_2346))) | ~v1_funct_1(E_2347))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_56782])).
% 22.69/13.89  tff(c_75479, plain, (![B_2419, A_2420, C_2421]: (k1_partfun1(B_2419, A_2420, '#skF_1', '#skF_2', k2_funct_1(C_2421), '#skF_3')=k5_relat_1(k2_funct_1(C_2421), '#skF_3') | ~v1_funct_1(k2_funct_1(C_2421)) | k2_relset_1(A_2420, B_2419, C_2421)!=B_2419 | ~v2_funct_1(C_2421) | ~m1_subset_1(C_2421, k1_zfmisc_1(k2_zfmisc_1(A_2420, B_2419))) | ~v1_funct_2(C_2421, A_2420, B_2419) | ~v1_funct_1(C_2421))), inference(resolution, [status(thm)], [c_120, c_65504])).
% 22.69/13.89  tff(c_75509, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_148, c_75479])).
% 22.69/13.89  tff(c_75535, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_150, c_136, c_140, c_51427, c_56917, c_75509])).
% 22.69/13.89  tff(c_110, plain, (![C_71, A_69, B_70, D_73]: (v2_funct_1(C_71) | ~r2_relset_1(A_69, A_69, k1_partfun1(A_69, B_70, B_70, A_69, C_71, D_73), k6_partfun1(A_69)) | ~m1_subset_1(D_73, k1_zfmisc_1(k2_zfmisc_1(B_70, A_69))) | ~v1_funct_2(D_73, B_70, A_69) | ~v1_funct_1(D_73) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~v1_funct_2(C_71, A_69, B_70) | ~v1_funct_1(C_71))), inference(cnfTransformation, [status(thm)], [f_278])).
% 22.69/13.89  tff(c_75548, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_75535, c_110])).
% 22.69/13.89  tff(c_75563, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_51427, c_56654, c_152, c_150, c_148, c_738, c_75548])).
% 22.69/13.89  tff(c_75564, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_66933, c_75563])).
% 22.69/13.89  tff(c_75570, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_120, c_75564])).
% 22.69/13.89  tff(c_75574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_150, c_148, c_136, c_140, c_75570])).
% 22.69/13.89  tff(c_75576, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_66932])).
% 22.69/13.89  tff(c_75579, plain, (k4_relat_1(k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_75576, c_40])).
% 22.69/13.89  tff(c_75582, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_542, c_51427, c_540, c_75579])).
% 22.69/13.89  tff(c_75575, plain, (k2_funct_1(k2_funct_1('#skF_3'))=k2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_66932])).
% 22.69/13.89  tff(c_75642, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_75582, c_75575])).
% 22.69/13.89  tff(c_75655, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k4_relat_1(k5_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_75642, c_54450])).
% 22.69/13.89  tff(c_75679, plain, (k4_relat_1(k5_relat_1('#skF_4', '#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56917, c_75655])).
% 22.69/13.89  tff(c_75681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57521, c_75679])).
% 22.69/13.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.69/13.89  
% 22.69/13.89  Inference rules
% 22.69/13.89  ----------------------
% 22.69/13.89  #Ref     : 0
% 22.69/13.89  #Sup     : 17840
% 22.69/13.89  #Fact    : 0
% 22.69/13.89  #Define  : 0
% 22.69/13.89  #Split   : 247
% 22.69/13.89  #Chain   : 0
% 22.69/13.89  #Close   : 0
% 22.69/13.89  
% 22.69/13.89  Ordering : KBO
% 22.69/13.89  
% 22.69/13.89  Simplification rules
% 22.69/13.89  ----------------------
% 22.69/13.89  #Subsume      : 1551
% 22.69/13.89  #Demod        : 29673
% 22.69/13.89  #Tautology    : 7303
% 22.69/13.89  #SimpNegUnit  : 381
% 22.69/13.89  #BackRed      : 695
% 22.69/13.89  
% 22.69/13.89  #Partial instantiations: 0
% 22.69/13.89  #Strategies tried      : 1
% 22.69/13.89  
% 22.69/13.89  Timing (in seconds)
% 22.69/13.89  ----------------------
% 23.01/13.89  Preprocessing        : 0.46
% 23.01/13.89  Parsing              : 0.24
% 23.01/13.89  CNF conversion       : 0.03
% 23.01/13.89  Main loop            : 12.58
% 23.01/13.89  Inferencing          : 2.72
% 23.01/13.89  Reduction            : 6.38
% 23.01/13.89  Demodulation         : 5.24
% 23.01/13.89  BG Simplification    : 0.26
% 23.01/13.89  Subsumption          : 2.55
% 23.01/13.89  Abstraction          : 0.40
% 23.01/13.89  MUC search           : 0.00
% 23.01/13.89  Cooper               : 0.00
% 23.01/13.89  Total                : 13.12
% 23.01/13.89  Index Insertion      : 0.00
% 23.01/13.89  Index Deletion       : 0.00
% 23.01/13.89  Index Matching       : 0.00
% 23.01/13.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
