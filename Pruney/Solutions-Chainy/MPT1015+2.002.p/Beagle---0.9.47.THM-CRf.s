%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:37 EST 2020

% Result     : Theorem 40.39s
% Output     : CNFRefutation 40.50s
% Verified   : 
% Statistics : Number of formulae       :  246 (11168 expanded)
%              Number of leaves         :   58 (4251 expanded)
%              Depth                    :   24
%              Number of atoms          :  636 (44320 expanded)
%              Number of equality atoms :  158 (5188 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k11_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_264,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,C,B),B)
                & v2_funct_1(B) )
             => r2_relset_1(A,A,C,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).

tff(f_168,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_152,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_156,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_244,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_160,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_228,axiom,(
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

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_174,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_236,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r1_tarski(k7_relset_1(A,B,D,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_2)).

tff(f_212,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_198,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_186,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
         => ( ! [D] :
                ( r2_hidden(D,A)
               => k11_relat_1(B,D) = k11_relat_1(C,D) )
           => r2_relset_1(A,A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( ( k1_relat_1(B) = A
              & k1_relat_1(C) = A
              & r1_tarski(k2_relat_1(C),A)
              & v2_funct_1(B)
              & k5_relat_1(C,B) = B )
           => C = k6_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).

tff(f_95,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_125,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_148,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & v2_funct_1(B) )
           => k2_funct_1(k5_relat_1(A,B)) = k5_relat_1(k2_funct_1(B),k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_133,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
          & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_202,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_30,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(c_86,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_228,plain,(
    ! [A_110,B_111,D_112] :
      ( r2_relset_1(A_110,B_111,D_112,D_112)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_242,plain,(
    r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_228])).

tff(c_92,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_105,plain,(
    ! [C_81,A_82,B_83] :
      ( v1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_125,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_105])).

tff(c_96,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_124,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_105])).

tff(c_90,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_88,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_273,plain,(
    ! [A_120,B_121,C_122] :
      ( k1_relset_1(A_120,B_121,C_122) = k1_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_292,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_273])).

tff(c_533,plain,(
    ! [A_153,B_154] :
      ( k1_relset_1(A_153,A_153,B_154) = A_153
      | ~ m1_subset_1(B_154,k1_zfmisc_1(k2_zfmisc_1(A_153,A_153)))
      | ~ v1_funct_2(B_154,A_153,A_153)
      | ~ v1_funct_1(B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_539,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_533])).

tff(c_555,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_292,c_539])).

tff(c_94,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_293,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_273])).

tff(c_542,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_533])).

tff(c_558,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_293,c_542])).

tff(c_300,plain,(
    ! [A_123,B_124,C_125] :
      ( k2_relset_1(A_123,B_124,C_125) = k2_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_319,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_300])).

tff(c_76924,plain,(
    ! [A_1611,C_1612,B_1613] :
      ( k6_partfun1(A_1611) = k5_relat_1(C_1612,k2_funct_1(C_1612))
      | k1_xboole_0 = B_1613
      | ~ v2_funct_1(C_1612)
      | k2_relset_1(A_1611,B_1613,C_1612) != B_1613
      | ~ m1_subset_1(C_1612,k1_zfmisc_1(k2_zfmisc_1(A_1611,B_1613)))
      | ~ v1_funct_2(C_1612,A_1611,B_1613)
      | ~ v1_funct_1(C_1612) ) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_76928,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_3','#skF_5') != '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_76924])).

tff(c_76941,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_5')
    | k2_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_319,c_76928])).

tff(c_76950,plain,(
    k2_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_76941])).

tff(c_16,plain,(
    ! [A_13] :
      ( v1_relat_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_495,plain,(
    ! [A_148,B_149,C_150] :
      ( k7_relset_1(A_148,B_149,C_150,A_148) = k2_relset_1(A_148,B_149,C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_499,plain,(
    k7_relset_1('#skF_3','#skF_3','#skF_5','#skF_3') = k2_relset_1('#skF_3','#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_495])).

tff(c_511,plain,(
    k7_relset_1('#skF_3','#skF_3','#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_499])).

tff(c_587,plain,(
    ! [A_155,B_156,D_157,C_158] :
      ( r1_tarski(k7_relset_1(A_155,B_156,D_157,C_158),B_156)
      | ~ m1_subset_1(D_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156)))
      | ~ v1_funct_2(D_157,A_155,B_156)
      | ~ v1_funct_1(D_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_591,plain,(
    ! [C_158] :
      ( r1_tarski(k7_relset_1('#skF_3','#skF_3','#skF_5',C_158),'#skF_3')
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_86,c_587])).

tff(c_613,plain,(
    ! [C_159] : r1_tarski(k7_relset_1('#skF_3','#skF_3','#skF_5',C_159),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_591])).

tff(c_615,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_613])).

tff(c_76685,plain,(
    ! [B_1583,F_1585,E_1584,D_1587,A_1586,C_1588] :
      ( k1_partfun1(A_1586,B_1583,C_1588,D_1587,E_1584,F_1585) = k5_relat_1(E_1584,F_1585)
      | ~ m1_subset_1(F_1585,k1_zfmisc_1(k2_zfmisc_1(C_1588,D_1587)))
      | ~ v1_funct_1(F_1585)
      | ~ m1_subset_1(E_1584,k1_zfmisc_1(k2_zfmisc_1(A_1586,B_1583)))
      | ~ v1_funct_1(E_1584) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_76689,plain,(
    ! [A_1586,B_1583,E_1584] :
      ( k1_partfun1(A_1586,B_1583,'#skF_3','#skF_3',E_1584,'#skF_5') = k5_relat_1(E_1584,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_1584,k1_zfmisc_1(k2_zfmisc_1(A_1586,B_1583)))
      | ~ v1_funct_1(E_1584) ) ),
    inference(resolution,[status(thm)],[c_86,c_76685])).

tff(c_77377,plain,(
    ! [A_1630,B_1631,E_1632] :
      ( k1_partfun1(A_1630,B_1631,'#skF_3','#skF_3',E_1632,'#skF_5') = k5_relat_1(E_1632,'#skF_5')
      | ~ m1_subset_1(E_1632,k1_zfmisc_1(k2_zfmisc_1(A_1630,B_1631)))
      | ~ v1_funct_1(E_1632) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_76689])).

tff(c_77386,plain,
    ( k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_5','#skF_5') = k5_relat_1('#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_77377])).

tff(c_77402,plain,(
    k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_5','#skF_5') = k5_relat_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_77386])).

tff(c_62,plain,(
    ! [A_50,B_51,E_54,C_52,D_53,F_55] :
      ( m1_subset_1(k1_partfun1(A_50,B_51,C_52,D_53,E_54,F_55),k1_zfmisc_1(k2_zfmisc_1(A_50,D_53)))
      | ~ m1_subset_1(F_55,k1_zfmisc_1(k2_zfmisc_1(C_52,D_53)))
      | ~ v1_funct_1(F_55)
      | ~ m1_subset_1(E_54,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ v1_funct_1(E_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_77412,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_77402,c_62])).

tff(c_77416,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_90,c_86,c_77412])).

tff(c_2953,plain,(
    ! [A_308,B_309,C_310] :
      ( r2_hidden('#skF_2'(A_308,B_309,C_310),A_308)
      | r2_relset_1(A_308,A_308,B_309,C_310)
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(A_308,A_308)))
      | ~ m1_subset_1(B_309,k1_zfmisc_1(k2_zfmisc_1(A_308,A_308))) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_2968,plain,(
    ! [B_309] :
      ( r2_hidden('#skF_2'('#skF_3',B_309,'#skF_4'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_3',B_309,'#skF_4')
      | ~ m1_subset_1(B_309,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_92,c_2953])).

tff(c_77495,plain,
    ( r2_hidden('#skF_2'('#skF_3',k5_relat_1('#skF_5','#skF_5'),'#skF_4'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_3',k5_relat_1('#skF_5','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_77416,c_2968])).

tff(c_77628,plain,(
    r2_relset_1('#skF_3','#skF_3',k5_relat_1('#skF_5','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_77495])).

tff(c_52,plain,(
    ! [D_39,C_38,A_36,B_37] :
      ( D_39 = C_38
      | ~ r2_relset_1(A_36,B_37,C_38,D_39)
      | ~ m1_subset_1(D_39,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_77630,plain,
    ( k5_relat_1('#skF_5','#skF_5') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k5_relat_1('#skF_5','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_77628,c_52])).

tff(c_77633,plain,(
    k5_relat_1('#skF_5','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77416,c_92,c_77630])).

tff(c_24,plain,(
    ! [C_18,B_16] :
      ( k6_relat_1(k1_relat_1(C_18)) = C_18
      | k5_relat_1(C_18,B_16) != B_16
      | ~ v2_funct_1(B_16)
      | ~ r1_tarski(k2_relat_1(C_18),k1_relat_1(C_18))
      | k1_relat_1(C_18) != k1_relat_1(B_16)
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_77647,plain,
    ( k6_relat_1(k1_relat_1('#skF_5')) = '#skF_5'
    | '#skF_5' != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_77633,c_24])).

tff(c_77652,plain,
    ( k6_relat_1('#skF_3') = '#skF_5'
    | '#skF_5' != '#skF_4'
    | ~ v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_90,c_615,c_555,c_555,c_77647])).

tff(c_77654,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_77652])).

tff(c_82,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_2777,plain,(
    ! [F_297,B_296,A_294,E_293,C_295,D_298] :
      ( m1_subset_1(k1_partfun1(A_294,B_296,C_295,D_298,E_293,F_297),k1_zfmisc_1(k2_zfmisc_1(A_294,D_298)))
      | ~ m1_subset_1(F_297,k1_zfmisc_1(k2_zfmisc_1(C_295,D_298)))
      | ~ v1_funct_1(F_297)
      | ~ m1_subset_1(E_293,k1_zfmisc_1(k2_zfmisc_1(A_294,B_296)))
      | ~ v1_funct_1(E_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_84,plain,(
    r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_630,plain,(
    ! [D_163,C_164,A_165,B_166] :
      ( D_163 = C_164
      | ~ r2_relset_1(A_165,B_166,C_164,D_163)
      | ~ m1_subset_1(D_163,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166)))
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_642,plain,
    ( k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_5','#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_84,c_630])).

tff(c_665,plain,
    ( k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_5','#skF_4') = '#skF_4'
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_642])).

tff(c_679,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_665])).

tff(c_2809,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2777,c_679])).

tff(c_2851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_96,c_92,c_2809])).

tff(c_2852,plain,(
    k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_5','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_665])).

tff(c_76691,plain,(
    ! [A_1586,B_1583,E_1584] :
      ( k1_partfun1(A_1586,B_1583,'#skF_3','#skF_3',E_1584,'#skF_4') = k5_relat_1(E_1584,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_1584,k1_zfmisc_1(k2_zfmisc_1(A_1586,B_1583)))
      | ~ v1_funct_1(E_1584) ) ),
    inference(resolution,[status(thm)],[c_92,c_76685])).

tff(c_77655,plain,(
    ! [A_1636,B_1637,E_1638] :
      ( k1_partfun1(A_1636,B_1637,'#skF_3','#skF_3',E_1638,'#skF_4') = k5_relat_1(E_1638,'#skF_4')
      | ~ m1_subset_1(E_1638,k1_zfmisc_1(k2_zfmisc_1(A_1636,B_1637)))
      | ~ v1_funct_1(E_1638) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_76691])).

tff(c_77667,plain,
    ( k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_5','#skF_4') = k5_relat_1('#skF_5','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_77655])).

tff(c_77686,plain,(
    k5_relat_1('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_2852,c_77667])).

tff(c_77694,plain,
    ( k6_relat_1(k1_relat_1('#skF_5')) = '#skF_5'
    | ~ v2_funct_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'))
    | k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_77686,c_24])).

tff(c_77699,plain,(
    k6_relat_1('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_96,c_124,c_90,c_555,c_558,c_615,c_555,c_82,c_555,c_77694])).

tff(c_26,plain,(
    ! [A_19] : v2_funct_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_77703,plain,(
    v2_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_77699,c_26])).

tff(c_77707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77654,c_77703])).

tff(c_77708,plain,
    ( '#skF_5' != '#skF_4'
    | k6_relat_1('#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_77652])).

tff(c_77711,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_77708])).

tff(c_320,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_300])).

tff(c_501,plain,(
    k7_relset_1('#skF_3','#skF_3','#skF_4','#skF_3') = k2_relset_1('#skF_3','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_495])).

tff(c_513,plain,(
    k7_relset_1('#skF_3','#skF_3','#skF_4','#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_501])).

tff(c_593,plain,(
    ! [C_158] :
      ( r1_tarski(k7_relset_1('#skF_3','#skF_3','#skF_4',C_158),'#skF_3')
      | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_92,c_587])).

tff(c_616,plain,(
    ! [C_160] : r1_tarski(k7_relset_1('#skF_3','#skF_3','#skF_4',C_160),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_593])).

tff(c_618,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_616])).

tff(c_77743,plain,(
    ! [A_1639,B_1640,E_1641] :
      ( k1_partfun1(A_1639,B_1640,'#skF_3','#skF_3',E_1641,'#skF_4') = k5_relat_1(E_1641,'#skF_4')
      | ~ m1_subset_1(E_1641,k1_zfmisc_1(k2_zfmisc_1(A_1639,B_1640)))
      | ~ v1_funct_1(E_1641) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_76691])).

tff(c_77752,plain,
    ( k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_5','#skF_4') = k5_relat_1('#skF_5','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_77743])).

tff(c_77768,plain,(
    k5_relat_1('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_2852,c_77752])).

tff(c_77776,plain,
    ( k6_relat_1(k1_relat_1('#skF_5')) = '#skF_5'
    | ~ v2_funct_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'))
    | k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_77768,c_24])).

tff(c_77781,plain,(
    k6_relat_1('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_96,c_124,c_90,c_555,c_558,c_615,c_555,c_82,c_555,c_77776])).

tff(c_38,plain,(
    ! [A_22] :
      ( k5_relat_1(A_22,k2_funct_1(A_22)) = k6_relat_1(k1_relat_1(A_22))
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_76778,plain,(
    ! [C_1595,B_1596] :
      ( k6_relat_1(k1_relat_1(C_1595)) = C_1595
      | k5_relat_1(C_1595,B_1596) != B_1596
      | ~ v2_funct_1(B_1596)
      | ~ r1_tarski(k2_relat_1(C_1595),k1_relat_1(C_1595))
      | k1_relat_1(C_1595) != k1_relat_1(B_1596)
      | ~ v1_funct_1(C_1595)
      | ~ v1_relat_1(C_1595)
      | ~ v1_funct_1(B_1596)
      | ~ v1_relat_1(B_1596) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_93898,plain,(
    ! [A_2001] :
      ( k6_relat_1(k1_relat_1(A_2001)) = A_2001
      | k6_relat_1(k1_relat_1(A_2001)) != k2_funct_1(A_2001)
      | ~ v2_funct_1(k2_funct_1(A_2001))
      | ~ r1_tarski(k2_relat_1(A_2001),k1_relat_1(A_2001))
      | k1_relat_1(k2_funct_1(A_2001)) != k1_relat_1(A_2001)
      | ~ v1_funct_1(A_2001)
      | ~ v1_relat_1(A_2001)
      | ~ v1_funct_1(k2_funct_1(A_2001))
      | ~ v1_relat_1(k2_funct_1(A_2001))
      | ~ v2_funct_1(A_2001)
      | ~ v1_funct_1(A_2001)
      | ~ v1_relat_1(A_2001) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_76778])).

tff(c_93970,plain,
    ( k6_relat_1(k1_relat_1('#skF_4')) = '#skF_4'
    | k6_relat_1(k1_relat_1('#skF_4')) != k2_funct_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_93898])).

tff(c_94025,plain,
    ( '#skF_5' = '#skF_4'
    | k2_funct_1('#skF_4') != '#skF_5'
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3'
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_96,c_82,c_125,c_96,c_558,c_618,c_77781,c_558,c_77781,c_558,c_93970])).

tff(c_94026,plain,
    ( k2_funct_1('#skF_4') != '#skF_5'
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3'
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_77711,c_94025])).

tff(c_94029,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_94026])).

tff(c_94032,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_94029])).

tff(c_94036,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_96,c_94032])).

tff(c_94038,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_94026])).

tff(c_14,plain,(
    ! [A_13] :
      ( v1_funct_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_77755,plain,
    ( k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4','#skF_4') = k5_relat_1('#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_77743])).

tff(c_77771,plain,(
    k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4','#skF_4') = k5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_77755])).

tff(c_77803,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_77771,c_62])).

tff(c_77807,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_96,c_92,c_77803])).

tff(c_2967,plain,(
    ! [B_309] :
      ( r2_hidden('#skF_2'('#skF_3',B_309,'#skF_5'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_3',B_309,'#skF_5')
      | ~ m1_subset_1(B_309,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_86,c_2953])).

tff(c_77893,plain,
    ( r2_hidden('#skF_2'('#skF_3',k5_relat_1('#skF_4','#skF_4'),'#skF_5'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_3',k5_relat_1('#skF_4','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_77807,c_2967])).

tff(c_77962,plain,(
    r2_relset_1('#skF_3','#skF_3',k5_relat_1('#skF_4','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_77893])).

tff(c_77964,plain,
    ( k5_relat_1('#skF_4','#skF_4') = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k5_relat_1('#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_77962,c_52])).

tff(c_77967,plain,(
    k5_relat_1('#skF_4','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77807,c_86,c_77964])).

tff(c_42,plain,(
    ! [B_26,A_24] :
      ( k5_relat_1(k2_funct_1(B_26),k2_funct_1(A_24)) = k2_funct_1(k5_relat_1(A_24,B_26))
      | ~ v2_funct_1(B_26)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_100379,plain,(
    ! [B_2090,A_2091] :
      ( k6_relat_1(k1_relat_1(k2_funct_1(B_2090))) = k2_funct_1(B_2090)
      | k2_funct_1(k5_relat_1(A_2091,B_2090)) != k2_funct_1(A_2091)
      | ~ v2_funct_1(k2_funct_1(A_2091))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(B_2090)),k1_relat_1(k2_funct_1(B_2090)))
      | k1_relat_1(k2_funct_1(B_2090)) != k1_relat_1(k2_funct_1(A_2091))
      | ~ v1_funct_1(k2_funct_1(B_2090))
      | ~ v1_relat_1(k2_funct_1(B_2090))
      | ~ v1_funct_1(k2_funct_1(A_2091))
      | ~ v1_relat_1(k2_funct_1(A_2091))
      | ~ v2_funct_1(B_2090)
      | ~ v2_funct_1(A_2091)
      | ~ v1_funct_1(B_2090)
      | ~ v1_relat_1(B_2090)
      | ~ v1_funct_1(A_2091)
      | ~ v1_relat_1(A_2091) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_76778])).

tff(c_100397,plain,
    ( k6_relat_1(k1_relat_1(k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | k2_funct_1('#skF_5') != k2_funct_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_77967,c_100379])).

tff(c_100416,plain,
    ( k6_relat_1(k1_relat_1(k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | k2_funct_1('#skF_5') != k2_funct_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_96,c_82,c_94038,c_100397])).

tff(c_101498,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_100416])).

tff(c_101501,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_101498])).

tff(c_101505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_96,c_101501])).

tff(c_101507,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_100416])).

tff(c_18,plain,(
    ! [A_14] :
      ( v2_funct_1(k2_funct_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    ! [A_23] :
      ( k2_funct_1(k2_funct_1(A_23)) = A_23
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_409,plain,(
    ! [A_138] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_138),A_138)) = k2_relat_1(A_138)
      | ~ v2_funct_1(A_138)
      | ~ v1_funct_1(A_138)
      | ~ v1_relat_1(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_78044,plain,(
    ! [A_1650] :
      ( k1_relat_1(k5_relat_1(A_1650,k2_funct_1(A_1650))) = k2_relat_1(k2_funct_1(A_1650))
      | ~ v2_funct_1(k2_funct_1(A_1650))
      | ~ v1_funct_1(k2_funct_1(A_1650))
      | ~ v1_relat_1(k2_funct_1(A_1650))
      | ~ v2_funct_1(A_1650)
      | ~ v1_funct_1(A_1650)
      | ~ v1_relat_1(A_1650) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_409])).

tff(c_105666,plain,(
    ! [A_2171] :
      ( k1_relat_1(k6_relat_1(k1_relat_1(A_2171))) = k2_relat_1(k2_funct_1(A_2171))
      | ~ v2_funct_1(k2_funct_1(A_2171))
      | ~ v1_funct_1(k2_funct_1(A_2171))
      | ~ v1_relat_1(k2_funct_1(A_2171))
      | ~ v2_funct_1(A_2171)
      | ~ v1_funct_1(A_2171)
      | ~ v1_relat_1(A_2171)
      | ~ v2_funct_1(A_2171)
      | ~ v1_funct_1(A_2171)
      | ~ v1_relat_1(A_2171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_78044])).

tff(c_105726,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1(k6_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_105666])).

tff(c_105765,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = '#skF_3'
    | ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_96,c_82,c_125,c_96,c_82,c_94038,c_101507,c_555,c_77781,c_105726])).

tff(c_105768,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_105765])).

tff(c_105771,plain,
    ( ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_105768])).

tff(c_105775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_96,c_82,c_105771])).

tff(c_105777,plain,(
    v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_105765])).

tff(c_105776,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_105765])).

tff(c_36,plain,(
    ! [A_22] :
      ( k5_relat_1(k2_funct_1(A_22),A_22) = k6_relat_1(k2_relat_1(A_22))
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_424,plain,(
    ! [A_139] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_139),A_139)) = k2_relat_1(A_139)
      | ~ v2_funct_1(A_139)
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_433,plain,(
    ! [A_22] :
      ( k2_relat_1(k6_relat_1(k2_relat_1(A_22))) = k2_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_424])).

tff(c_2928,plain,(
    ! [A_303] :
      ( k1_relat_1(k6_relat_1(k2_relat_1(A_303))) = k2_relat_1(A_303)
      | ~ v2_funct_1(A_303)
      | ~ v1_funct_1(A_303)
      | ~ v1_relat_1(A_303)
      | ~ v2_funct_1(A_303)
      | ~ v1_funct_1(A_303)
      | ~ v1_relat_1(A_303) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_409])).

tff(c_2937,plain,(
    ! [A_22] :
      ( k2_relat_1(k6_relat_1(k2_relat_1(A_22))) = k1_relat_1(k6_relat_1(k2_relat_1(A_22)))
      | ~ v2_funct_1(k6_relat_1(k2_relat_1(A_22)))
      | ~ v1_funct_1(k6_relat_1(k2_relat_1(A_22)))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_22)))
      | ~ v2_funct_1(k6_relat_1(k2_relat_1(A_22)))
      | ~ v1_funct_1(k6_relat_1(k2_relat_1(A_22)))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_22)))
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_2928])).

tff(c_2947,plain,(
    ! [A_22] :
      ( k2_relat_1(k6_relat_1(k2_relat_1(A_22))) = k1_relat_1(k6_relat_1(k2_relat_1(A_22)))
      | ~ v1_funct_1(k6_relat_1(k2_relat_1(A_22)))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_22)))
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_2937])).

tff(c_105817,plain,
    ( k2_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_4')))) = k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_4'))))
    | ~ v1_funct_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_4'))))
    | ~ v1_relat_1(k6_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_105776,c_2947])).

tff(c_105843,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94038,c_101507,c_105777,c_124,c_77781,c_90,c_77781,c_105776,c_555,c_77781,c_105776,c_77781,c_105776,c_105817])).

tff(c_105845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76950,c_105843])).

tff(c_105847,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_76941])).

tff(c_105848,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105847,c_615])).

tff(c_418,plain,(
    ! [A_22] :
      ( k1_relat_1(k6_relat_1(k2_relat_1(A_22))) = k2_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_409])).

tff(c_105854,plain,
    ( k1_relat_1(k6_relat_1('#skF_3')) = k2_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_105847,c_418])).

tff(c_105861,plain,
    ( k1_relat_1(k6_relat_1('#skF_3')) = '#skF_3'
    | ~ v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_90,c_124,c_90,c_105847,c_105854])).

tff(c_105901,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_105861])).

tff(c_106478,plain,(
    ! [A_2195,B_2196,E_2197] :
      ( k1_partfun1(A_2195,B_2196,'#skF_3','#skF_3',E_2197,'#skF_4') = k5_relat_1(E_2197,'#skF_4')
      | ~ m1_subset_1(E_2197,k1_zfmisc_1(k2_zfmisc_1(A_2195,B_2196)))
      | ~ v1_funct_1(E_2197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_76691])).

tff(c_106487,plain,
    ( k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_5','#skF_4') = k5_relat_1('#skF_5','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_106478])).

tff(c_106503,plain,(
    k5_relat_1('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_2852,c_106487])).

tff(c_106511,plain,
    ( k6_relat_1(k1_relat_1('#skF_5')) = '#skF_5'
    | ~ v2_funct_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'))
    | k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_106503,c_24])).

tff(c_106516,plain,(
    k6_relat_1('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_96,c_124,c_90,c_555,c_558,c_105848,c_105847,c_555,c_82,c_555,c_106511])).

tff(c_106520,plain,(
    v2_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_106516,c_26])).

tff(c_106524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105901,c_106520])).

tff(c_106526,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_105861])).

tff(c_105850,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105847,c_319])).

tff(c_105876,plain,(
    ! [B_2173,C_2174,A_2175] :
      ( k6_partfun1(B_2173) = k5_relat_1(k2_funct_1(C_2174),C_2174)
      | k1_xboole_0 = B_2173
      | ~ v2_funct_1(C_2174)
      | k2_relset_1(A_2175,B_2173,C_2174) != B_2173
      | ~ m1_subset_1(C_2174,k1_zfmisc_1(k2_zfmisc_1(A_2175,B_2173)))
      | ~ v1_funct_2(C_2174,A_2175,B_2173)
      | ~ v1_funct_1(C_2174) ) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_105880,plain,
    ( k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_3','#skF_5') != '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_105876])).

tff(c_105893,plain,
    ( k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_105850,c_105880])).

tff(c_106528,plain,
    ( k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106526,c_105893])).

tff(c_106529,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_106528])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_161,plain,(
    ! [C_91,B_92,A_93] :
      ( ~ v1_xboole_0(C_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(C_91))
      | ~ r2_hidden(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_176,plain,(
    ! [A_3,A_93] :
      ( ~ v1_xboole_0(A_3)
      | ~ r2_hidden(A_93,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_161])).

tff(c_177,plain,(
    ! [A_93] : ~ r2_hidden(A_93,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_106547,plain,(
    ! [A_93] : ~ r2_hidden(A_93,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106529,c_177])).

tff(c_68,plain,(
    ! [A_56] : m1_subset_1(k6_partfun1(A_56),k1_zfmisc_1(k2_zfmisc_1(A_56,A_56))) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_2971,plain,(
    ! [B_311] :
      ( r2_hidden('#skF_2'('#skF_3',B_311,'#skF_5'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_3',B_311,'#skF_5')
      | ~ m1_subset_1(B_311,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_86,c_2953])).

tff(c_2990,plain,
    ( r2_hidden('#skF_2'('#skF_3',k6_partfun1('#skF_3'),'#skF_5'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_2971])).

tff(c_76707,plain,(
    r2_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2990])).

tff(c_76709,plain,
    ( k6_partfun1('#skF_3') = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_76707,c_52])).

tff(c_76712,plain,(
    k6_partfun1('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_86,c_76709])).

tff(c_80,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_5',k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_76743,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76712,c_80])).

tff(c_76748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_76743])).

tff(c_76749,plain,(
    r2_hidden('#skF_2'('#skF_3',k6_partfun1('#skF_3'),'#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_2990])).

tff(c_106561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106547,c_76749])).

tff(c_106562,plain,(
    k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_106528])).

tff(c_106680,plain,
    ( k6_relat_1(k2_relat_1('#skF_5')) = k6_partfun1('#skF_3')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_106562,c_36])).

tff(c_106693,plain,(
    k6_relat_1('#skF_3') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_90,c_106526,c_105847,c_106680])).

tff(c_107025,plain,(
    ! [A_2211,B_2212,E_2213] :
      ( k1_partfun1(A_2211,B_2212,'#skF_3','#skF_3',E_2213,'#skF_4') = k5_relat_1(E_2213,'#skF_4')
      | ~ m1_subset_1(E_2213,k1_zfmisc_1(k2_zfmisc_1(A_2211,B_2212)))
      | ~ v1_funct_1(E_2213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_76691])).

tff(c_107034,plain,
    ( k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_5','#skF_4') = k5_relat_1('#skF_5','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_107025])).

tff(c_107050,plain,(
    k5_relat_1('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_2852,c_107034])).

tff(c_107058,plain,
    ( k6_relat_1(k1_relat_1('#skF_5')) = '#skF_5'
    | ~ v2_funct_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'))
    | k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_107050,c_24])).

tff(c_107063,plain,(
    k6_partfun1('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_96,c_124,c_90,c_555,c_558,c_105848,c_555,c_105847,c_82,c_106693,c_555,c_107058])).

tff(c_76750,plain,(
    ~ r2_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_2990])).

tff(c_107072,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107063,c_76750])).

tff(c_107081,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_107072])).

tff(c_107082,plain,(
    ! [A_3] : ~ v1_xboole_0(A_3) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_130,plain,(
    ! [B_87,A_88] :
      ( v1_xboole_0(B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_88))
      | ~ v1_xboole_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_151,plain,(
    ! [A_3] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_130])).

tff(c_152,plain,(
    ! [A_3] : ~ v1_xboole_0(A_3) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_2,plain,(
    ! [A_1] : v1_xboole_0('#skF_1'(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_2])).

tff(c_157,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_107087,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107082,c_157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:17:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 40.39/25.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.50/25.17  
% 40.50/25.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.50/25.17  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k11_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 40.50/25.17  
% 40.50/25.17  %Foreground sorts:
% 40.50/25.17  
% 40.50/25.17  
% 40.50/25.17  %Background operators:
% 40.50/25.17  
% 40.50/25.17  
% 40.50/25.17  %Foreground operators:
% 40.50/25.17  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 40.50/25.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 40.50/25.17  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 40.50/25.17  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 40.50/25.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 40.50/25.17  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 40.50/25.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 40.50/25.17  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 40.50/25.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 40.50/25.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 40.50/25.17  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 40.50/25.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 40.50/25.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 40.50/25.17  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 40.50/25.17  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 40.50/25.17  tff('#skF_5', type, '#skF_5': $i).
% 40.50/25.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 40.50/25.17  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 40.50/25.17  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 40.50/25.17  tff('#skF_3', type, '#skF_3': $i).
% 40.50/25.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 40.50/25.17  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 40.50/25.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 40.50/25.17  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 40.50/25.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 40.50/25.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 40.50/25.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 40.50/25.17  tff('#skF_4', type, '#skF_4': $i).
% 40.50/25.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 40.50/25.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 40.50/25.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 40.50/25.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 40.50/25.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 40.50/25.17  
% 40.50/25.20  tff(f_264, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r2_relset_1(A, A, k1_partfun1(A, A, A, A, C, B), B) & v2_funct_1(B)) => r2_relset_1(A, A, C, k6_partfun1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_funct_2)).
% 40.50/25.20  tff(f_168, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 40.50/25.20  tff(f_152, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 40.50/25.20  tff(f_156, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 40.50/25.20  tff(f_244, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 40.50/25.20  tff(f_160, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 40.50/25.20  tff(f_228, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 40.50/25.20  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 40.50/25.20  tff(f_174, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 40.50/25.20  tff(f_236, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k7_relset_1(A, B, D, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_funct_2)).
% 40.50/25.20  tff(f_212, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 40.50/25.20  tff(f_198, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 40.50/25.20  tff(f_186, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => ((![D]: (r2_hidden(D, A) => (k11_relat_1(B, D) = k11_relat_1(C, D)))) => r2_relset_1(A, A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relset_1)).
% 40.50/25.20  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) & r1_tarski(k2_relat_1(C), A)) & v2_funct_1(B)) & (k5_relat_1(C, B) = B)) => (C = k6_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_1)).
% 40.50/25.20  tff(f_95, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 40.50/25.20  tff(f_125, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 40.50/25.20  tff(f_148, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(A) & v2_funct_1(B)) => (k2_funct_1(k5_relat_1(A, B)) = k5_relat_1(k2_funct_1(B), k2_funct_1(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_funct_1)).
% 40.50/25.20  tff(f_72, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 40.50/25.20  tff(f_133, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 40.50/25.20  tff(f_115, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 40.50/25.20  tff(f_32, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 40.50/25.20  tff(f_52, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 40.50/25.20  tff(f_202, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 40.50/25.20  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 40.50/25.20  tff(f_30, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 40.50/25.20  tff(c_86, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_264])).
% 40.50/25.20  tff(c_228, plain, (![A_110, B_111, D_112]: (r2_relset_1(A_110, B_111, D_112, D_112) | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_168])).
% 40.50/25.20  tff(c_242, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_86, c_228])).
% 40.50/25.20  tff(c_92, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_264])).
% 40.50/25.20  tff(c_105, plain, (![C_81, A_82, B_83]: (v1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 40.50/25.20  tff(c_125, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_105])).
% 40.50/25.20  tff(c_96, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_264])).
% 40.50/25.20  tff(c_124, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_105])).
% 40.50/25.20  tff(c_90, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_264])).
% 40.50/25.20  tff(c_88, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_264])).
% 40.50/25.20  tff(c_273, plain, (![A_120, B_121, C_122]: (k1_relset_1(A_120, B_121, C_122)=k1_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 40.50/25.20  tff(c_292, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_273])).
% 40.50/25.20  tff(c_533, plain, (![A_153, B_154]: (k1_relset_1(A_153, A_153, B_154)=A_153 | ~m1_subset_1(B_154, k1_zfmisc_1(k2_zfmisc_1(A_153, A_153))) | ~v1_funct_2(B_154, A_153, A_153) | ~v1_funct_1(B_154))), inference(cnfTransformation, [status(thm)], [f_244])).
% 40.50/25.20  tff(c_539, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_533])).
% 40.50/25.20  tff(c_555, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_292, c_539])).
% 40.50/25.20  tff(c_94, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_264])).
% 40.50/25.20  tff(c_293, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_273])).
% 40.50/25.20  tff(c_542, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_533])).
% 40.50/25.20  tff(c_558, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_293, c_542])).
% 40.50/25.20  tff(c_300, plain, (![A_123, B_124, C_125]: (k2_relset_1(A_123, B_124, C_125)=k2_relat_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 40.50/25.20  tff(c_319, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_300])).
% 40.50/25.20  tff(c_76924, plain, (![A_1611, C_1612, B_1613]: (k6_partfun1(A_1611)=k5_relat_1(C_1612, k2_funct_1(C_1612)) | k1_xboole_0=B_1613 | ~v2_funct_1(C_1612) | k2_relset_1(A_1611, B_1613, C_1612)!=B_1613 | ~m1_subset_1(C_1612, k1_zfmisc_1(k2_zfmisc_1(A_1611, B_1613))) | ~v1_funct_2(C_1612, A_1611, B_1613) | ~v1_funct_1(C_1612))), inference(cnfTransformation, [status(thm)], [f_228])).
% 40.50/25.20  tff(c_76928, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_3', '#skF_5')!='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_76924])).
% 40.50/25.20  tff(c_76941, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_5') | k2_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_319, c_76928])).
% 40.50/25.20  tff(c_76950, plain, (k2_relat_1('#skF_5')!='#skF_3'), inference(splitLeft, [status(thm)], [c_76941])).
% 40.50/25.20  tff(c_16, plain, (![A_13]: (v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 40.50/25.20  tff(c_495, plain, (![A_148, B_149, C_150]: (k7_relset_1(A_148, B_149, C_150, A_148)=k2_relset_1(A_148, B_149, C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 40.50/25.20  tff(c_499, plain, (k7_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_3')=k2_relset_1('#skF_3', '#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_86, c_495])).
% 40.50/25.20  tff(c_511, plain, (k7_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_319, c_499])).
% 40.50/25.20  tff(c_587, plain, (![A_155, B_156, D_157, C_158]: (r1_tarski(k7_relset_1(A_155, B_156, D_157, C_158), B_156) | ~m1_subset_1(D_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))) | ~v1_funct_2(D_157, A_155, B_156) | ~v1_funct_1(D_157))), inference(cnfTransformation, [status(thm)], [f_236])).
% 40.50/25.20  tff(c_591, plain, (![C_158]: (r1_tarski(k7_relset_1('#skF_3', '#skF_3', '#skF_5', C_158), '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_86, c_587])).
% 40.50/25.20  tff(c_613, plain, (![C_159]: (r1_tarski(k7_relset_1('#skF_3', '#skF_3', '#skF_5', C_159), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_591])).
% 40.50/25.20  tff(c_615, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_511, c_613])).
% 40.50/25.20  tff(c_76685, plain, (![B_1583, F_1585, E_1584, D_1587, A_1586, C_1588]: (k1_partfun1(A_1586, B_1583, C_1588, D_1587, E_1584, F_1585)=k5_relat_1(E_1584, F_1585) | ~m1_subset_1(F_1585, k1_zfmisc_1(k2_zfmisc_1(C_1588, D_1587))) | ~v1_funct_1(F_1585) | ~m1_subset_1(E_1584, k1_zfmisc_1(k2_zfmisc_1(A_1586, B_1583))) | ~v1_funct_1(E_1584))), inference(cnfTransformation, [status(thm)], [f_212])).
% 40.50/25.20  tff(c_76689, plain, (![A_1586, B_1583, E_1584]: (k1_partfun1(A_1586, B_1583, '#skF_3', '#skF_3', E_1584, '#skF_5')=k5_relat_1(E_1584, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_1584, k1_zfmisc_1(k2_zfmisc_1(A_1586, B_1583))) | ~v1_funct_1(E_1584))), inference(resolution, [status(thm)], [c_86, c_76685])).
% 40.50/25.20  tff(c_77377, plain, (![A_1630, B_1631, E_1632]: (k1_partfun1(A_1630, B_1631, '#skF_3', '#skF_3', E_1632, '#skF_5')=k5_relat_1(E_1632, '#skF_5') | ~m1_subset_1(E_1632, k1_zfmisc_1(k2_zfmisc_1(A_1630, B_1631))) | ~v1_funct_1(E_1632))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_76689])).
% 40.50/25.20  tff(c_77386, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_5', '#skF_5')=k5_relat_1('#skF_5', '#skF_5') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_77377])).
% 40.50/25.20  tff(c_77402, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_5', '#skF_5')=k5_relat_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_77386])).
% 40.50/25.20  tff(c_62, plain, (![A_50, B_51, E_54, C_52, D_53, F_55]: (m1_subset_1(k1_partfun1(A_50, B_51, C_52, D_53, E_54, F_55), k1_zfmisc_1(k2_zfmisc_1(A_50, D_53))) | ~m1_subset_1(F_55, k1_zfmisc_1(k2_zfmisc_1(C_52, D_53))) | ~v1_funct_1(F_55) | ~m1_subset_1(E_54, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | ~v1_funct_1(E_54))), inference(cnfTransformation, [status(thm)], [f_198])).
% 40.50/25.20  tff(c_77412, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_77402, c_62])).
% 40.50/25.20  tff(c_77416, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_90, c_86, c_77412])).
% 40.50/25.20  tff(c_2953, plain, (![A_308, B_309, C_310]: (r2_hidden('#skF_2'(A_308, B_309, C_310), A_308) | r2_relset_1(A_308, A_308, B_309, C_310) | ~m1_subset_1(C_310, k1_zfmisc_1(k2_zfmisc_1(A_308, A_308))) | ~m1_subset_1(B_309, k1_zfmisc_1(k2_zfmisc_1(A_308, A_308))))), inference(cnfTransformation, [status(thm)], [f_186])).
% 40.50/25.20  tff(c_2968, plain, (![B_309]: (r2_hidden('#skF_2'('#skF_3', B_309, '#skF_4'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', B_309, '#skF_4') | ~m1_subset_1(B_309, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(resolution, [status(thm)], [c_92, c_2953])).
% 40.50/25.20  tff(c_77495, plain, (r2_hidden('#skF_2'('#skF_3', k5_relat_1('#skF_5', '#skF_5'), '#skF_4'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', k5_relat_1('#skF_5', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_77416, c_2968])).
% 40.50/25.20  tff(c_77628, plain, (r2_relset_1('#skF_3', '#skF_3', k5_relat_1('#skF_5', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_77495])).
% 40.50/25.20  tff(c_52, plain, (![D_39, C_38, A_36, B_37]: (D_39=C_38 | ~r2_relset_1(A_36, B_37, C_38, D_39) | ~m1_subset_1(D_39, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_168])).
% 40.50/25.20  tff(c_77630, plain, (k5_relat_1('#skF_5', '#skF_5')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k5_relat_1('#skF_5', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_77628, c_52])).
% 40.50/25.20  tff(c_77633, plain, (k5_relat_1('#skF_5', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_77416, c_92, c_77630])).
% 40.50/25.20  tff(c_24, plain, (![C_18, B_16]: (k6_relat_1(k1_relat_1(C_18))=C_18 | k5_relat_1(C_18, B_16)!=B_16 | ~v2_funct_1(B_16) | ~r1_tarski(k2_relat_1(C_18), k1_relat_1(C_18)) | k1_relat_1(C_18)!=k1_relat_1(B_16) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_93])).
% 40.50/25.20  tff(c_77647, plain, (k6_relat_1(k1_relat_1('#skF_5'))='#skF_5' | '#skF_5'!='#skF_4' | ~v2_funct_1('#skF_5') | ~r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_77633, c_24])).
% 40.50/25.20  tff(c_77652, plain, (k6_relat_1('#skF_3')='#skF_5' | '#skF_5'!='#skF_4' | ~v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_90, c_615, c_555, c_555, c_77647])).
% 40.50/25.20  tff(c_77654, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_77652])).
% 40.50/25.20  tff(c_82, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_264])).
% 40.50/25.20  tff(c_2777, plain, (![F_297, B_296, A_294, E_293, C_295, D_298]: (m1_subset_1(k1_partfun1(A_294, B_296, C_295, D_298, E_293, F_297), k1_zfmisc_1(k2_zfmisc_1(A_294, D_298))) | ~m1_subset_1(F_297, k1_zfmisc_1(k2_zfmisc_1(C_295, D_298))) | ~v1_funct_1(F_297) | ~m1_subset_1(E_293, k1_zfmisc_1(k2_zfmisc_1(A_294, B_296))) | ~v1_funct_1(E_293))), inference(cnfTransformation, [status(thm)], [f_198])).
% 40.50/25.20  tff(c_84, plain, (r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_264])).
% 40.50/25.20  tff(c_630, plain, (![D_163, C_164, A_165, B_166]: (D_163=C_164 | ~r2_relset_1(A_165, B_166, C_164, D_163) | ~m1_subset_1(D_163, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_168])).
% 40.50/25.20  tff(c_642, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_5', '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_84, c_630])).
% 40.50/25.20  tff(c_665, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_5', '#skF_4')='#skF_4' | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_642])).
% 40.50/25.20  tff(c_679, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_665])).
% 40.50/25.20  tff(c_2809, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_2777, c_679])).
% 40.50/25.20  tff(c_2851, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_96, c_92, c_2809])).
% 40.50/25.20  tff(c_2852, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_5', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_665])).
% 40.50/25.20  tff(c_76691, plain, (![A_1586, B_1583, E_1584]: (k1_partfun1(A_1586, B_1583, '#skF_3', '#skF_3', E_1584, '#skF_4')=k5_relat_1(E_1584, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_1584, k1_zfmisc_1(k2_zfmisc_1(A_1586, B_1583))) | ~v1_funct_1(E_1584))), inference(resolution, [status(thm)], [c_92, c_76685])).
% 40.50/25.20  tff(c_77655, plain, (![A_1636, B_1637, E_1638]: (k1_partfun1(A_1636, B_1637, '#skF_3', '#skF_3', E_1638, '#skF_4')=k5_relat_1(E_1638, '#skF_4') | ~m1_subset_1(E_1638, k1_zfmisc_1(k2_zfmisc_1(A_1636, B_1637))) | ~v1_funct_1(E_1638))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_76691])).
% 40.50/25.20  tff(c_77667, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_5', '#skF_4')=k5_relat_1('#skF_5', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_77655])).
% 40.50/25.20  tff(c_77686, plain, (k5_relat_1('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_2852, c_77667])).
% 40.50/25.20  tff(c_77694, plain, (k6_relat_1(k1_relat_1('#skF_5'))='#skF_5' | ~v2_funct_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_77686, c_24])).
% 40.50/25.20  tff(c_77699, plain, (k6_relat_1('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_96, c_124, c_90, c_555, c_558, c_615, c_555, c_82, c_555, c_77694])).
% 40.50/25.20  tff(c_26, plain, (![A_19]: (v2_funct_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 40.50/25.20  tff(c_77703, plain, (v2_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_77699, c_26])).
% 40.50/25.20  tff(c_77707, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77654, c_77703])).
% 40.50/25.20  tff(c_77708, plain, ('#skF_5'!='#skF_4' | k6_relat_1('#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_77652])).
% 40.50/25.20  tff(c_77711, plain, ('#skF_5'!='#skF_4'), inference(splitLeft, [status(thm)], [c_77708])).
% 40.50/25.20  tff(c_320, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_300])).
% 40.50/25.20  tff(c_501, plain, (k7_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_3')=k2_relset_1('#skF_3', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_92, c_495])).
% 40.50/25.20  tff(c_513, plain, (k7_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_320, c_501])).
% 40.50/25.20  tff(c_593, plain, (![C_158]: (r1_tarski(k7_relset_1('#skF_3', '#skF_3', '#skF_4', C_158), '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_92, c_587])).
% 40.50/25.20  tff(c_616, plain, (![C_160]: (r1_tarski(k7_relset_1('#skF_3', '#skF_3', '#skF_4', C_160), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_593])).
% 40.50/25.20  tff(c_618, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_513, c_616])).
% 40.50/25.20  tff(c_77743, plain, (![A_1639, B_1640, E_1641]: (k1_partfun1(A_1639, B_1640, '#skF_3', '#skF_3', E_1641, '#skF_4')=k5_relat_1(E_1641, '#skF_4') | ~m1_subset_1(E_1641, k1_zfmisc_1(k2_zfmisc_1(A_1639, B_1640))) | ~v1_funct_1(E_1641))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_76691])).
% 40.50/25.20  tff(c_77752, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_5', '#skF_4')=k5_relat_1('#skF_5', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_77743])).
% 40.50/25.20  tff(c_77768, plain, (k5_relat_1('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_2852, c_77752])).
% 40.50/25.20  tff(c_77776, plain, (k6_relat_1(k1_relat_1('#skF_5'))='#skF_5' | ~v2_funct_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_77768, c_24])).
% 40.50/25.20  tff(c_77781, plain, (k6_relat_1('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_96, c_124, c_90, c_555, c_558, c_615, c_555, c_82, c_555, c_77776])).
% 40.50/25.21  tff(c_38, plain, (![A_22]: (k5_relat_1(A_22, k2_funct_1(A_22))=k6_relat_1(k1_relat_1(A_22)) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_125])).
% 40.50/25.21  tff(c_76778, plain, (![C_1595, B_1596]: (k6_relat_1(k1_relat_1(C_1595))=C_1595 | k5_relat_1(C_1595, B_1596)!=B_1596 | ~v2_funct_1(B_1596) | ~r1_tarski(k2_relat_1(C_1595), k1_relat_1(C_1595)) | k1_relat_1(C_1595)!=k1_relat_1(B_1596) | ~v1_funct_1(C_1595) | ~v1_relat_1(C_1595) | ~v1_funct_1(B_1596) | ~v1_relat_1(B_1596))), inference(cnfTransformation, [status(thm)], [f_93])).
% 40.50/25.21  tff(c_93898, plain, (![A_2001]: (k6_relat_1(k1_relat_1(A_2001))=A_2001 | k6_relat_1(k1_relat_1(A_2001))!=k2_funct_1(A_2001) | ~v2_funct_1(k2_funct_1(A_2001)) | ~r1_tarski(k2_relat_1(A_2001), k1_relat_1(A_2001)) | k1_relat_1(k2_funct_1(A_2001))!=k1_relat_1(A_2001) | ~v1_funct_1(A_2001) | ~v1_relat_1(A_2001) | ~v1_funct_1(k2_funct_1(A_2001)) | ~v1_relat_1(k2_funct_1(A_2001)) | ~v2_funct_1(A_2001) | ~v1_funct_1(A_2001) | ~v1_relat_1(A_2001))), inference(superposition, [status(thm), theory('equality')], [c_38, c_76778])).
% 40.50/25.21  tff(c_93970, plain, (k6_relat_1(k1_relat_1('#skF_4'))='#skF_4' | k6_relat_1(k1_relat_1('#skF_4'))!=k2_funct_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_558, c_93898])).
% 40.50/25.21  tff(c_94025, plain, ('#skF_5'='#skF_4' | k2_funct_1('#skF_4')!='#skF_5' | ~v2_funct_1(k2_funct_1('#skF_4')) | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3' | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_96, c_82, c_125, c_96, c_558, c_618, c_77781, c_558, c_77781, c_558, c_93970])).
% 40.50/25.21  tff(c_94026, plain, (k2_funct_1('#skF_4')!='#skF_5' | ~v2_funct_1(k2_funct_1('#skF_4')) | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3' | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_77711, c_94025])).
% 40.50/25.21  tff(c_94029, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_94026])).
% 40.50/25.21  tff(c_94032, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_94029])).
% 40.50/25.21  tff(c_94036, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_96, c_94032])).
% 40.50/25.21  tff(c_94038, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_94026])).
% 40.50/25.21  tff(c_14, plain, (![A_13]: (v1_funct_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 40.50/25.21  tff(c_77755, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_4')=k5_relat_1('#skF_4', '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_77743])).
% 40.50/25.21  tff(c_77771, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_4')=k5_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_77755])).
% 40.50/25.21  tff(c_77803, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_77771, c_62])).
% 40.50/25.21  tff(c_77807, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_96, c_92, c_77803])).
% 40.50/25.21  tff(c_2967, plain, (![B_309]: (r2_hidden('#skF_2'('#skF_3', B_309, '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', B_309, '#skF_5') | ~m1_subset_1(B_309, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(resolution, [status(thm)], [c_86, c_2953])).
% 40.50/25.21  tff(c_77893, plain, (r2_hidden('#skF_2'('#skF_3', k5_relat_1('#skF_4', '#skF_4'), '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', k5_relat_1('#skF_4', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_77807, c_2967])).
% 40.50/25.21  tff(c_77962, plain, (r2_relset_1('#skF_3', '#skF_3', k5_relat_1('#skF_4', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_77893])).
% 40.50/25.21  tff(c_77964, plain, (k5_relat_1('#skF_4', '#skF_4')='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k5_relat_1('#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_77962, c_52])).
% 40.50/25.21  tff(c_77967, plain, (k5_relat_1('#skF_4', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_77807, c_86, c_77964])).
% 40.50/25.21  tff(c_42, plain, (![B_26, A_24]: (k5_relat_1(k2_funct_1(B_26), k2_funct_1(A_24))=k2_funct_1(k5_relat_1(A_24, B_26)) | ~v2_funct_1(B_26) | ~v2_funct_1(A_24) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_148])).
% 40.50/25.21  tff(c_100379, plain, (![B_2090, A_2091]: (k6_relat_1(k1_relat_1(k2_funct_1(B_2090)))=k2_funct_1(B_2090) | k2_funct_1(k5_relat_1(A_2091, B_2090))!=k2_funct_1(A_2091) | ~v2_funct_1(k2_funct_1(A_2091)) | ~r1_tarski(k2_relat_1(k2_funct_1(B_2090)), k1_relat_1(k2_funct_1(B_2090))) | k1_relat_1(k2_funct_1(B_2090))!=k1_relat_1(k2_funct_1(A_2091)) | ~v1_funct_1(k2_funct_1(B_2090)) | ~v1_relat_1(k2_funct_1(B_2090)) | ~v1_funct_1(k2_funct_1(A_2091)) | ~v1_relat_1(k2_funct_1(A_2091)) | ~v2_funct_1(B_2090) | ~v2_funct_1(A_2091) | ~v1_funct_1(B_2090) | ~v1_relat_1(B_2090) | ~v1_funct_1(A_2091) | ~v1_relat_1(A_2091))), inference(superposition, [status(thm), theory('equality')], [c_42, c_76778])).
% 40.50/25.21  tff(c_100397, plain, (k6_relat_1(k1_relat_1(k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | k2_funct_1('#skF_5')!=k2_funct_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_4')), k1_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_77967, c_100379])).
% 40.50/25.21  tff(c_100416, plain, (k6_relat_1(k1_relat_1(k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | k2_funct_1('#skF_5')!=k2_funct_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_4')), k1_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_96, c_82, c_94038, c_100397])).
% 40.50/25.21  tff(c_101498, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_100416])).
% 40.50/25.21  tff(c_101501, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_101498])).
% 40.50/25.21  tff(c_101505, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_96, c_101501])).
% 40.50/25.21  tff(c_101507, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_100416])).
% 40.50/25.21  tff(c_18, plain, (![A_14]: (v2_funct_1(k2_funct_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 40.50/25.21  tff(c_40, plain, (![A_23]: (k2_funct_1(k2_funct_1(A_23))=A_23 | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_133])).
% 40.50/25.21  tff(c_409, plain, (![A_138]: (k1_relat_1(k5_relat_1(k2_funct_1(A_138), A_138))=k2_relat_1(A_138) | ~v2_funct_1(A_138) | ~v1_funct_1(A_138) | ~v1_relat_1(A_138))), inference(cnfTransformation, [status(thm)], [f_115])).
% 40.50/25.21  tff(c_78044, plain, (![A_1650]: (k1_relat_1(k5_relat_1(A_1650, k2_funct_1(A_1650)))=k2_relat_1(k2_funct_1(A_1650)) | ~v2_funct_1(k2_funct_1(A_1650)) | ~v1_funct_1(k2_funct_1(A_1650)) | ~v1_relat_1(k2_funct_1(A_1650)) | ~v2_funct_1(A_1650) | ~v1_funct_1(A_1650) | ~v1_relat_1(A_1650))), inference(superposition, [status(thm), theory('equality')], [c_40, c_409])).
% 40.50/25.21  tff(c_105666, plain, (![A_2171]: (k1_relat_1(k6_relat_1(k1_relat_1(A_2171)))=k2_relat_1(k2_funct_1(A_2171)) | ~v2_funct_1(k2_funct_1(A_2171)) | ~v1_funct_1(k2_funct_1(A_2171)) | ~v1_relat_1(k2_funct_1(A_2171)) | ~v2_funct_1(A_2171) | ~v1_funct_1(A_2171) | ~v1_relat_1(A_2171) | ~v2_funct_1(A_2171) | ~v1_funct_1(A_2171) | ~v1_relat_1(A_2171))), inference(superposition, [status(thm), theory('equality')], [c_38, c_78044])).
% 40.50/25.21  tff(c_105726, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1(k6_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_558, c_105666])).
% 40.50/25.21  tff(c_105765, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_3' | ~v2_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_96, c_82, c_125, c_96, c_82, c_94038, c_101507, c_555, c_77781, c_105726])).
% 40.50/25.21  tff(c_105768, plain, (~v2_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_105765])).
% 40.50/25.21  tff(c_105771, plain, (~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_105768])).
% 40.50/25.21  tff(c_105775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_96, c_82, c_105771])).
% 40.50/25.21  tff(c_105777, plain, (v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_105765])).
% 40.50/25.21  tff(c_105776, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_105765])).
% 40.50/25.21  tff(c_36, plain, (![A_22]: (k5_relat_1(k2_funct_1(A_22), A_22)=k6_relat_1(k2_relat_1(A_22)) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_125])).
% 40.50/25.21  tff(c_424, plain, (![A_139]: (k2_relat_1(k5_relat_1(k2_funct_1(A_139), A_139))=k2_relat_1(A_139) | ~v2_funct_1(A_139) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_115])).
% 40.50/25.21  tff(c_433, plain, (![A_22]: (k2_relat_1(k6_relat_1(k2_relat_1(A_22)))=k2_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(superposition, [status(thm), theory('equality')], [c_36, c_424])).
% 40.50/25.21  tff(c_2928, plain, (![A_303]: (k1_relat_1(k6_relat_1(k2_relat_1(A_303)))=k2_relat_1(A_303) | ~v2_funct_1(A_303) | ~v1_funct_1(A_303) | ~v1_relat_1(A_303) | ~v2_funct_1(A_303) | ~v1_funct_1(A_303) | ~v1_relat_1(A_303))), inference(superposition, [status(thm), theory('equality')], [c_36, c_409])).
% 40.50/25.21  tff(c_2937, plain, (![A_22]: (k2_relat_1(k6_relat_1(k2_relat_1(A_22)))=k1_relat_1(k6_relat_1(k2_relat_1(A_22))) | ~v2_funct_1(k6_relat_1(k2_relat_1(A_22))) | ~v1_funct_1(k6_relat_1(k2_relat_1(A_22))) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_22))) | ~v2_funct_1(k6_relat_1(k2_relat_1(A_22))) | ~v1_funct_1(k6_relat_1(k2_relat_1(A_22))) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_22))) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(superposition, [status(thm), theory('equality')], [c_433, c_2928])).
% 40.50/25.21  tff(c_2947, plain, (![A_22]: (k2_relat_1(k6_relat_1(k2_relat_1(A_22)))=k1_relat_1(k6_relat_1(k2_relat_1(A_22))) | ~v1_funct_1(k6_relat_1(k2_relat_1(A_22))) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_22))) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_2937])).
% 40.50/25.21  tff(c_105817, plain, (k2_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_4'))))=k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_4')))) | ~v1_funct_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_4')))) | ~v1_relat_1(k6_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_105776, c_2947])).
% 40.50/25.21  tff(c_105843, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_94038, c_101507, c_105777, c_124, c_77781, c_90, c_77781, c_105776, c_555, c_77781, c_105776, c_77781, c_105776, c_105817])).
% 40.50/25.21  tff(c_105845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76950, c_105843])).
% 40.50/25.21  tff(c_105847, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_76941])).
% 40.50/25.21  tff(c_105848, plain, (r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_105847, c_615])).
% 40.50/25.21  tff(c_418, plain, (![A_22]: (k1_relat_1(k6_relat_1(k2_relat_1(A_22)))=k2_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(superposition, [status(thm), theory('equality')], [c_36, c_409])).
% 40.50/25.21  tff(c_105854, plain, (k1_relat_1(k6_relat_1('#skF_3'))=k2_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_105847, c_418])).
% 40.50/25.21  tff(c_105861, plain, (k1_relat_1(k6_relat_1('#skF_3'))='#skF_3' | ~v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_90, c_124, c_90, c_105847, c_105854])).
% 40.50/25.21  tff(c_105901, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_105861])).
% 40.50/25.21  tff(c_106478, plain, (![A_2195, B_2196, E_2197]: (k1_partfun1(A_2195, B_2196, '#skF_3', '#skF_3', E_2197, '#skF_4')=k5_relat_1(E_2197, '#skF_4') | ~m1_subset_1(E_2197, k1_zfmisc_1(k2_zfmisc_1(A_2195, B_2196))) | ~v1_funct_1(E_2197))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_76691])).
% 40.50/25.21  tff(c_106487, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_5', '#skF_4')=k5_relat_1('#skF_5', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_106478])).
% 40.50/25.21  tff(c_106503, plain, (k5_relat_1('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_2852, c_106487])).
% 40.50/25.21  tff(c_106511, plain, (k6_relat_1(k1_relat_1('#skF_5'))='#skF_5' | ~v2_funct_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_106503, c_24])).
% 40.50/25.21  tff(c_106516, plain, (k6_relat_1('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_96, c_124, c_90, c_555, c_558, c_105848, c_105847, c_555, c_82, c_555, c_106511])).
% 40.50/25.21  tff(c_106520, plain, (v2_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_106516, c_26])).
% 40.50/25.21  tff(c_106524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105901, c_106520])).
% 40.50/25.21  tff(c_106526, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_105861])).
% 40.50/25.21  tff(c_105850, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_105847, c_319])).
% 40.50/25.21  tff(c_105876, plain, (![B_2173, C_2174, A_2175]: (k6_partfun1(B_2173)=k5_relat_1(k2_funct_1(C_2174), C_2174) | k1_xboole_0=B_2173 | ~v2_funct_1(C_2174) | k2_relset_1(A_2175, B_2173, C_2174)!=B_2173 | ~m1_subset_1(C_2174, k1_zfmisc_1(k2_zfmisc_1(A_2175, B_2173))) | ~v1_funct_2(C_2174, A_2175, B_2173) | ~v1_funct_1(C_2174))), inference(cnfTransformation, [status(thm)], [f_228])).
% 40.50/25.21  tff(c_105880, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_3', '#skF_5')!='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_105876])).
% 40.50/25.21  tff(c_105893, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_105850, c_105880])).
% 40.50/25.21  tff(c_106528, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_106526, c_105893])).
% 40.50/25.21  tff(c_106529, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_106528])).
% 40.50/25.21  tff(c_6, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 40.50/25.21  tff(c_161, plain, (![C_91, B_92, A_93]: (~v1_xboole_0(C_91) | ~m1_subset_1(B_92, k1_zfmisc_1(C_91)) | ~r2_hidden(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_52])).
% 40.50/25.21  tff(c_176, plain, (![A_3, A_93]: (~v1_xboole_0(A_3) | ~r2_hidden(A_93, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_161])).
% 40.50/25.21  tff(c_177, plain, (![A_93]: (~r2_hidden(A_93, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_176])).
% 40.50/25.21  tff(c_106547, plain, (![A_93]: (~r2_hidden(A_93, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_106529, c_177])).
% 40.50/25.21  tff(c_68, plain, (![A_56]: (m1_subset_1(k6_partfun1(A_56), k1_zfmisc_1(k2_zfmisc_1(A_56, A_56))))), inference(cnfTransformation, [status(thm)], [f_202])).
% 40.50/25.21  tff(c_2971, plain, (![B_311]: (r2_hidden('#skF_2'('#skF_3', B_311, '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', B_311, '#skF_5') | ~m1_subset_1(B_311, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(resolution, [status(thm)], [c_86, c_2953])).
% 40.50/25.21  tff(c_2990, plain, (r2_hidden('#skF_2'('#skF_3', k6_partfun1('#skF_3'), '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_68, c_2971])).
% 40.50/25.21  tff(c_76707, plain, (r2_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_2990])).
% 40.50/25.21  tff(c_76709, plain, (k6_partfun1('#skF_3')='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_76707, c_52])).
% 40.50/25.21  tff(c_76712, plain, (k6_partfun1('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_86, c_76709])).
% 40.50/25.21  tff(c_80, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_5', k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_264])).
% 40.50/25.21  tff(c_76743, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76712, c_80])).
% 40.50/25.21  tff(c_76748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_242, c_76743])).
% 40.50/25.21  tff(c_76749, plain, (r2_hidden('#skF_2'('#skF_3', k6_partfun1('#skF_3'), '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_2990])).
% 40.50/25.21  tff(c_106561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106547, c_76749])).
% 40.50/25.21  tff(c_106562, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_106528])).
% 40.50/25.21  tff(c_106680, plain, (k6_relat_1(k2_relat_1('#skF_5'))=k6_partfun1('#skF_3') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_106562, c_36])).
% 40.50/25.21  tff(c_106693, plain, (k6_relat_1('#skF_3')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_90, c_106526, c_105847, c_106680])).
% 40.50/25.21  tff(c_107025, plain, (![A_2211, B_2212, E_2213]: (k1_partfun1(A_2211, B_2212, '#skF_3', '#skF_3', E_2213, '#skF_4')=k5_relat_1(E_2213, '#skF_4') | ~m1_subset_1(E_2213, k1_zfmisc_1(k2_zfmisc_1(A_2211, B_2212))) | ~v1_funct_1(E_2213))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_76691])).
% 40.50/25.21  tff(c_107034, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_5', '#skF_4')=k5_relat_1('#skF_5', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_107025])).
% 40.50/25.21  tff(c_107050, plain, (k5_relat_1('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_2852, c_107034])).
% 40.50/25.21  tff(c_107058, plain, (k6_relat_1(k1_relat_1('#skF_5'))='#skF_5' | ~v2_funct_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_107050, c_24])).
% 40.50/25.21  tff(c_107063, plain, (k6_partfun1('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_96, c_124, c_90, c_555, c_558, c_105848, c_555, c_105847, c_82, c_106693, c_555, c_107058])).
% 40.50/25.21  tff(c_76750, plain, (~r2_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_2990])).
% 40.50/25.21  tff(c_107072, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_107063, c_76750])).
% 40.50/25.21  tff(c_107081, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_242, c_107072])).
% 40.50/25.21  tff(c_107082, plain, (![A_3]: (~v1_xboole_0(A_3))), inference(splitRight, [status(thm)], [c_176])).
% 40.50/25.21  tff(c_130, plain, (![B_87, A_88]: (v1_xboole_0(B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(A_88)) | ~v1_xboole_0(A_88))), inference(cnfTransformation, [status(thm)], [f_39])).
% 40.50/25.21  tff(c_151, plain, (![A_3]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_6, c_130])).
% 40.50/25.21  tff(c_152, plain, (![A_3]: (~v1_xboole_0(A_3))), inference(splitLeft, [status(thm)], [c_151])).
% 40.50/25.21  tff(c_2, plain, (![A_1]: (v1_xboole_0('#skF_1'(A_1)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 40.50/25.21  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_152, c_2])).
% 40.50/25.21  tff(c_157, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_151])).
% 40.50/25.21  tff(c_107087, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107082, c_157])).
% 40.50/25.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.50/25.21  
% 40.50/25.21  Inference rules
% 40.50/25.21  ----------------------
% 40.50/25.21  #Ref     : 9
% 40.50/25.21  #Sup     : 30368
% 40.50/25.21  #Fact    : 0
% 40.50/25.21  #Define  : 0
% 40.50/25.21  #Split   : 125
% 40.50/25.21  #Chain   : 0
% 40.50/25.21  #Close   : 0
% 40.50/25.21  
% 40.50/25.21  Ordering : KBO
% 40.50/25.21  
% 40.50/25.21  Simplification rules
% 40.50/25.21  ----------------------
% 40.50/25.21  #Subsume      : 7625
% 40.50/25.21  #Demod        : 37818
% 40.50/25.21  #Tautology    : 3573
% 40.50/25.21  #SimpNegUnit  : 134
% 40.50/25.21  #BackRed      : 972
% 40.50/25.21  
% 40.50/25.21  #Partial instantiations: 0
% 40.50/25.21  #Strategies tried      : 1
% 40.50/25.21  
% 40.50/25.21  Timing (in seconds)
% 40.50/25.21  ----------------------
% 40.75/25.21  Preprocessing        : 0.41
% 40.75/25.21  Parsing              : 0.21
% 40.75/25.21  CNF conversion       : 0.03
% 40.75/25.21  Main loop            : 23.91
% 40.75/25.21  Inferencing          : 4.04
% 40.75/25.21  Reduction            : 10.13
% 40.75/25.21  Demodulation         : 8.32
% 40.75/25.21  BG Simplification    : 0.69
% 40.75/25.21  Subsumption          : 8.07
% 40.75/25.21  Abstraction          : 0.91
% 40.75/25.21  MUC search           : 0.00
% 40.75/25.21  Cooper               : 0.00
% 40.75/25.21  Total                : 24.39
% 40.75/25.21  Index Insertion      : 0.00
% 40.75/25.21  Index Deletion       : 0.00
% 40.75/25.21  Index Matching       : 0.00
% 40.75/25.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
