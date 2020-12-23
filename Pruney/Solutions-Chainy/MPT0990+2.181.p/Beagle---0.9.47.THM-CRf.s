%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:23 EST 2020

% Result     : Theorem 18.70s
% Output     : CNFRefutation 18.70s
% Verified   : 
% Statistics : Number of formulae       :  187 (3765 expanded)
%              Number of leaves         :   50 (1348 expanded)
%              Depth                    :   24
%              Number of atoms          :  447 (15460 expanded)
%              Number of equality atoms :  141 (4539 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_322,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_177,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_209,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_211,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_187,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_185,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_199,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_270,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_254,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_228,axiom,(
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

tff(f_286,axiom,(
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

tff(f_296,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_150,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(c_100,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_122,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_110,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_118,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_784,plain,(
    ! [A_113,B_114,C_115] :
      ( k2_relset_1(A_113,B_114,C_115) = k2_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_796,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_784])).

tff(c_802,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_796])).

tff(c_116,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_112,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_1913,plain,(
    ! [C_162,B_159,D_161,A_160,E_163,F_164] :
      ( k1_partfun1(A_160,B_159,C_162,D_161,E_163,F_164) = k5_relat_1(E_163,F_164)
      | ~ m1_subset_1(F_164,k1_zfmisc_1(k2_zfmisc_1(C_162,D_161)))
      | ~ v1_funct_1(F_164)
      | ~ m1_subset_1(E_163,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159)))
      | ~ v1_funct_1(E_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_1923,plain,(
    ! [A_160,B_159,E_163] :
      ( k1_partfun1(A_160,B_159,'#skF_2','#skF_1',E_163,'#skF_4') = k5_relat_1(E_163,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_163,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159)))
      | ~ v1_funct_1(E_163) ) ),
    inference(resolution,[status(thm)],[c_112,c_1913])).

tff(c_2052,plain,(
    ! [A_173,B_174,E_175] :
      ( k1_partfun1(A_173,B_174,'#skF_2','#skF_1',E_175,'#skF_4') = k5_relat_1(E_175,'#skF_4')
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ v1_funct_1(E_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_1923])).

tff(c_2073,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_2052])).

tff(c_2090,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_2073])).

tff(c_72,plain,(
    ! [A_51] : k6_relat_1(A_51) = k6_partfun1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_64,plain,(
    ! [A_38] : m1_subset_1(k6_relat_1(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_123,plain,(
    ! [A_38] : m1_subset_1(k6_partfun1(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_64])).

tff(c_108,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_1010,plain,(
    ! [D_121,C_122,A_123,B_124] :
      ( D_121 = C_122
      | ~ r2_relset_1(A_123,B_124,C_122,D_121)
      | ~ m1_subset_1(D_121,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124)))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_1024,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_108,c_1010])).

tff(c_1049,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_1024])).

tff(c_1109,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1049])).

tff(c_2097,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2090,c_1109])).

tff(c_2387,plain,(
    ! [C_187,A_185,D_188,F_189,E_190,B_186] :
      ( m1_subset_1(k1_partfun1(A_185,B_186,C_187,D_188,E_190,F_189),k1_zfmisc_1(k2_zfmisc_1(A_185,D_188)))
      | ~ m1_subset_1(F_189,k1_zfmisc_1(k2_zfmisc_1(C_187,D_188)))
      | ~ v1_funct_1(F_189)
      | ~ m1_subset_1(E_190,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186)))
      | ~ v1_funct_1(E_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_2430,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2090,c_2387])).

tff(c_2454,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_118,c_116,c_112,c_2430])).

tff(c_2456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2097,c_2454])).

tff(c_2457,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1049])).

tff(c_9547,plain,(
    ! [A_481,B_480,D_482,F_485,C_483,E_484] :
      ( k1_partfun1(A_481,B_480,C_483,D_482,E_484,F_485) = k5_relat_1(E_484,F_485)
      | ~ m1_subset_1(F_485,k1_zfmisc_1(k2_zfmisc_1(C_483,D_482)))
      | ~ v1_funct_1(F_485)
      | ~ m1_subset_1(E_484,k1_zfmisc_1(k2_zfmisc_1(A_481,B_480)))
      | ~ v1_funct_1(E_484) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_9559,plain,(
    ! [A_481,B_480,E_484] :
      ( k1_partfun1(A_481,B_480,'#skF_2','#skF_1',E_484,'#skF_4') = k5_relat_1(E_484,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_484,k1_zfmisc_1(k2_zfmisc_1(A_481,B_480)))
      | ~ v1_funct_1(E_484) ) ),
    inference(resolution,[status(thm)],[c_112,c_9547])).

tff(c_10300,plain,(
    ! [A_519,B_520,E_521] :
      ( k1_partfun1(A_519,B_520,'#skF_2','#skF_1',E_521,'#skF_4') = k5_relat_1(E_521,'#skF_4')
      | ~ m1_subset_1(E_521,k1_zfmisc_1(k2_zfmisc_1(A_519,B_520)))
      | ~ v1_funct_1(E_521) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_9559])).

tff(c_10324,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_10300])).

tff(c_10342,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_2457,c_10324])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_212,plain,(
    ! [B_85,A_86] :
      ( v1_relat_1(B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_86))
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_221,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_118,c_212])).

tff(c_230,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_221])).

tff(c_18,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_131,plain,(
    ! [A_10] : k2_relat_1(k6_partfun1(A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_18])).

tff(c_104,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_114,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_800,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_112,c_784])).

tff(c_2792,plain,(
    ! [C_199,A_200,B_201] :
      ( v1_funct_1(k2_funct_1(C_199))
      | k2_relset_1(A_200,B_201,C_199) != B_201
      | ~ v2_funct_1(C_199)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201)))
      | ~ v1_funct_2(C_199,A_200,B_201)
      | ~ v1_funct_1(C_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_2807,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_112,c_2792])).

tff(c_2823,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_114,c_800,c_2807])).

tff(c_2838,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2823])).

tff(c_120,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_36,plain,(
    ! [A_16] : v2_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_125,plain,(
    ! [A_16] : v2_funct_1(k6_partfun1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_36])).

tff(c_5912,plain,(
    ! [D_346,B_343,E_344,A_345,C_347] :
      ( k1_xboole_0 = C_347
      | v2_funct_1(E_344)
      | k2_relset_1(A_345,B_343,D_346) != B_343
      | ~ v2_funct_1(k1_partfun1(A_345,B_343,B_343,C_347,D_346,E_344))
      | ~ m1_subset_1(E_344,k1_zfmisc_1(k2_zfmisc_1(B_343,C_347)))
      | ~ v1_funct_2(E_344,B_343,C_347)
      | ~ v1_funct_1(E_344)
      | ~ m1_subset_1(D_346,k1_zfmisc_1(k2_zfmisc_1(A_345,B_343)))
      | ~ v1_funct_2(D_346,A_345,B_343)
      | ~ v1_funct_1(D_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_5919,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_2457,c_5912])).

tff(c_5927,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_118,c_116,c_114,c_112,c_125,c_110,c_5919])).

tff(c_5929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2838,c_104,c_5927])).

tff(c_5930,plain,
    ( k2_relat_1('#skF_4') != '#skF_1'
    | v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2823])).

tff(c_5983,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5930])).

tff(c_658,plain,(
    ! [A_107,B_108,D_109] :
      ( r2_relset_1(A_107,B_108,D_109,D_109)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_665,plain,(
    ! [A_38] : r2_relset_1(A_38,A_38,k6_partfun1(A_38),k6_partfun1(A_38)) ),
    inference(resolution,[status(thm)],[c_123,c_658])).

tff(c_7951,plain,(
    ! [A_421,B_422,C_423,D_424] :
      ( k2_relset_1(A_421,B_422,C_423) = B_422
      | ~ r2_relset_1(B_422,B_422,k1_partfun1(B_422,A_421,A_421,B_422,D_424,C_423),k6_partfun1(B_422))
      | ~ m1_subset_1(D_424,k1_zfmisc_1(k2_zfmisc_1(B_422,A_421)))
      | ~ v1_funct_2(D_424,B_422,A_421)
      | ~ v1_funct_1(D_424)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(k2_zfmisc_1(A_421,B_422)))
      | ~ v1_funct_2(C_423,A_421,B_422)
      | ~ v1_funct_1(C_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_7957,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2457,c_7951])).

tff(c_7961,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_114,c_112,c_122,c_120,c_118,c_665,c_800,c_7957])).

tff(c_7963,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5983,c_7961])).

tff(c_7965,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5930])).

tff(c_7966,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7965,c_800])).

tff(c_5931,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2823])).

tff(c_9651,plain,(
    ! [A_489,C_490,B_491] :
      ( k6_partfun1(A_489) = k5_relat_1(C_490,k2_funct_1(C_490))
      | k1_xboole_0 = B_491
      | ~ v2_funct_1(C_490)
      | k2_relset_1(A_489,B_491,C_490) != B_491
      | ~ m1_subset_1(C_490,k1_zfmisc_1(k2_zfmisc_1(A_489,B_491)))
      | ~ v1_funct_2(C_490,A_489,B_491)
      | ~ v1_funct_1(C_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_9663,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_112,c_9651])).

tff(c_9681,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_114,c_7966,c_5931,c_9663])).

tff(c_9682,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_9681])).

tff(c_218,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_112,c_212])).

tff(c_227,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_218])).

tff(c_96,plain,(
    ! [A_69] :
      ( v1_funct_2(A_69,k1_relat_1(A_69),k2_relat_1(A_69))
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_7985,plain,
    ( v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7965,c_96])).

tff(c_8005,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_116,c_7985])).

tff(c_94,plain,(
    ! [A_69] :
      ( m1_subset_1(A_69,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_69),k2_relat_1(A_69))))
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_797,plain,(
    ! [A_69] :
      ( k2_relset_1(k1_relat_1(A_69),k2_relat_1(A_69),A_69) = k2_relat_1(A_69)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(resolution,[status(thm)],[c_94,c_784])).

tff(c_7976,plain,
    ( k2_relset_1(k1_relat_1('#skF_4'),'#skF_1','#skF_4') = k2_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7965,c_797])).

tff(c_7999,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),'#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_116,c_7965,c_7976])).

tff(c_7982,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7965,c_94])).

tff(c_8003,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_116,c_7982])).

tff(c_9657,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4'))
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(k1_relat_1('#skF_4'),'#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8003,c_9651])).

tff(c_9673,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4'))
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_8005,c_7999,c_5931,c_9657])).

tff(c_9674,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_9673])).

tff(c_9733,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9682,c_9674])).

tff(c_9779,plain,(
    k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9733,c_131])).

tff(c_9802,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_9779])).

tff(c_52,plain,(
    ! [A_24,B_26] :
      ( k2_funct_1(A_24) = B_26
      | k6_relat_1(k2_relat_1(A_24)) != k5_relat_1(B_26,A_24)
      | k2_relat_1(B_26) != k1_relat_1(A_24)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_8132,plain,(
    ! [A_425,B_426] :
      ( k2_funct_1(A_425) = B_426
      | k6_partfun1(k2_relat_1(A_425)) != k5_relat_1(B_426,A_425)
      | k2_relat_1(B_426) != k1_relat_1(A_425)
      | ~ v2_funct_1(A_425)
      | ~ v1_funct_1(B_426)
      | ~ v1_relat_1(B_426)
      | ~ v1_funct_1(A_425)
      | ~ v1_relat_1(A_425) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_52])).

tff(c_8134,plain,(
    ! [B_426] :
      ( k2_funct_1('#skF_4') = B_426
      | k5_relat_1(B_426,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_426) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_426)
      | ~ v1_relat_1(B_426)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7965,c_8132])).

tff(c_8166,plain,(
    ! [B_426] :
      ( k2_funct_1('#skF_4') = B_426
      | k5_relat_1(B_426,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_426) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_426)
      | ~ v1_relat_1(B_426) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_116,c_5931,c_8134])).

tff(c_31574,plain,(
    ! [B_921] :
      ( k2_funct_1('#skF_4') = B_921
      | k5_relat_1(B_921,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_921) != '#skF_2'
      | ~ v1_funct_1(B_921)
      | ~ v1_relat_1(B_921) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9802,c_8166])).

tff(c_31742,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_230,c_31574])).

tff(c_31917,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_802,c_10342,c_31742])).

tff(c_28,plain,(
    ! [A_14] :
      ( v1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    ! [A_13] :
      ( k4_relat_1(A_13) = k2_funct_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5934,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5931,c_24])).

tff(c_5937,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_116,c_5934])).

tff(c_6,plain,(
    ! [A_6] :
      ( k4_relat_1(k4_relat_1(A_6)) = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5965,plain,
    ( k4_relat_1(k2_funct_1('#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5937,c_6])).

tff(c_5981,plain,(
    k4_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_5965])).

tff(c_12,plain,(
    ! [A_9] :
      ( k2_relat_1(k4_relat_1(A_9)) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_5962,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5937,c_12])).

tff(c_5979,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_5962])).

tff(c_14,plain,(
    ! [A_9] :
      ( k1_relat_1(k4_relat_1(A_9)) = k2_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_248,plain,(
    ! [A_88] :
      ( k9_relat_1(A_88,k1_relat_1(A_88)) = k2_relat_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_257,plain,(
    ! [A_9] :
      ( k9_relat_1(k4_relat_1(A_9),k2_relat_1(A_9)) = k2_relat_1(k4_relat_1(A_9))
      | ~ v1_relat_1(k4_relat_1(A_9))
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_248])).

tff(c_8396,plain,
    ( k9_relat_1(k4_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4')) = k2_relat_1(k4_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5979,c_257])).

tff(c_8428,plain,
    ( k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_5981,c_7965,c_5981,c_5981,c_8396])).

tff(c_9641,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8428])).

tff(c_9644,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_9641])).

tff(c_9648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_116,c_9644])).

tff(c_9650,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_8428])).

tff(c_7964,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5930])).

tff(c_38,plain,(
    ! [A_17] :
      ( v2_funct_1(k2_funct_1(A_17))
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_102,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_8474,plain,(
    ! [C_430,B_431,A_432] :
      ( v1_funct_2(k2_funct_1(C_430),B_431,A_432)
      | k2_relset_1(A_432,B_431,C_430) != B_431
      | ~ v2_funct_1(C_430)
      | ~ m1_subset_1(C_430,k1_zfmisc_1(k2_zfmisc_1(A_432,B_431)))
      | ~ v1_funct_2(C_430,A_432,B_431)
      | ~ v1_funct_1(C_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_8492,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_1','#skF_2')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_112,c_8474])).

tff(c_8511,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_114,c_5931,c_7966,c_8492])).

tff(c_9814,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9802,c_5979])).

tff(c_5959,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5937,c_14])).

tff(c_5977,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_5959])).

tff(c_8337,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7965,c_5977])).

tff(c_9912,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2',k2_funct_1('#skF_4')) = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9814,c_797])).

tff(c_9943,plain,(
    k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9650,c_7964,c_9814,c_8337,c_9912])).

tff(c_9918,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9814,c_94])).

tff(c_9947,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9650,c_7964,c_8337,c_9918])).

tff(c_92,plain,(
    ! [A_66,C_68,B_67] :
      ( k6_partfun1(A_66) = k5_relat_1(C_68,k2_funct_1(C_68))
      | k1_xboole_0 = B_67
      | ~ v2_funct_1(C_68)
      | k2_relset_1(A_66,B_67,C_68) != B_67
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ v1_funct_2(C_68,A_66,B_67)
      | ~ v1_funct_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_10112,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) != '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_1','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_9947,c_92])).

tff(c_10143,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7964,c_8511,c_9943,c_10112])).

tff(c_10144,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_10143])).

tff(c_10167,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_10144])).

tff(c_10170,plain,
    ( ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_10167])).

tff(c_10174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_116,c_5931,c_10170])).

tff(c_10176,plain,(
    v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_10144])).

tff(c_10179,plain,
    ( k4_relat_1(k2_funct_1('#skF_4')) = k2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_10176,c_24])).

tff(c_10182,plain,(
    k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9650,c_7964,c_5981,c_10179])).

tff(c_31970,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31917,c_10182])).

tff(c_32011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_31970])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:12:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.70/10.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.70/10.43  
% 18.70/10.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.70/10.43  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 18.70/10.43  
% 18.70/10.43  %Foreground sorts:
% 18.70/10.43  
% 18.70/10.43  
% 18.70/10.43  %Background operators:
% 18.70/10.43  
% 18.70/10.43  
% 18.70/10.43  %Foreground operators:
% 18.70/10.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 18.70/10.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 18.70/10.43  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 18.70/10.43  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 18.70/10.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.70/10.43  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 18.70/10.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.70/10.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 18.70/10.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 18.70/10.43  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 18.70/10.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 18.70/10.43  tff('#skF_2', type, '#skF_2': $i).
% 18.70/10.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 18.70/10.43  tff('#skF_3', type, '#skF_3': $i).
% 18.70/10.43  tff('#skF_1', type, '#skF_1': $i).
% 18.70/10.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.70/10.43  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 18.70/10.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.70/10.43  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 18.70/10.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.70/10.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 18.70/10.43  tff('#skF_4', type, '#skF_4': $i).
% 18.70/10.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 18.70/10.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.70/10.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 18.70/10.43  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 18.70/10.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.70/10.43  
% 18.70/10.46  tff(f_322, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 18.70/10.46  tff(f_177, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 18.70/10.46  tff(f_209, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 18.70/10.46  tff(f_211, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 18.70/10.46  tff(f_187, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 18.70/10.46  tff(f_185, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 18.70/10.46  tff(f_199, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 18.70/10.46  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 18.70/10.46  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 18.70/10.46  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 18.70/10.46  tff(f_270, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 18.70/10.46  tff(f_88, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 18.70/10.46  tff(f_254, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 18.70/10.46  tff(f_228, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 18.70/10.46  tff(f_286, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 18.70/10.46  tff(f_296, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 18.70/10.46  tff(f_150, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 18.70/10.46  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 18.70/10.46  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 18.70/10.46  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 18.70/10.46  tff(f_52, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 18.70/10.46  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 18.70/10.46  tff(f_100, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 18.70/10.46  tff(c_100, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_322])).
% 18.70/10.46  tff(c_122, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_322])).
% 18.70/10.46  tff(c_110, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_322])).
% 18.70/10.46  tff(c_118, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_322])).
% 18.70/10.46  tff(c_784, plain, (![A_113, B_114, C_115]: (k2_relset_1(A_113, B_114, C_115)=k2_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_177])).
% 18.70/10.46  tff(c_796, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_118, c_784])).
% 18.70/10.46  tff(c_802, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_796])).
% 18.70/10.46  tff(c_116, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_322])).
% 18.70/10.46  tff(c_112, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_322])).
% 18.70/10.46  tff(c_1913, plain, (![C_162, B_159, D_161, A_160, E_163, F_164]: (k1_partfun1(A_160, B_159, C_162, D_161, E_163, F_164)=k5_relat_1(E_163, F_164) | ~m1_subset_1(F_164, k1_zfmisc_1(k2_zfmisc_1(C_162, D_161))) | ~v1_funct_1(F_164) | ~m1_subset_1(E_163, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))) | ~v1_funct_1(E_163))), inference(cnfTransformation, [status(thm)], [f_209])).
% 18.70/10.46  tff(c_1923, plain, (![A_160, B_159, E_163]: (k1_partfun1(A_160, B_159, '#skF_2', '#skF_1', E_163, '#skF_4')=k5_relat_1(E_163, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_163, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))) | ~v1_funct_1(E_163))), inference(resolution, [status(thm)], [c_112, c_1913])).
% 18.70/10.46  tff(c_2052, plain, (![A_173, B_174, E_175]: (k1_partfun1(A_173, B_174, '#skF_2', '#skF_1', E_175, '#skF_4')=k5_relat_1(E_175, '#skF_4') | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~v1_funct_1(E_175))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_1923])).
% 18.70/10.46  tff(c_2073, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_118, c_2052])).
% 18.70/10.46  tff(c_2090, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_2073])).
% 18.70/10.46  tff(c_72, plain, (![A_51]: (k6_relat_1(A_51)=k6_partfun1(A_51))), inference(cnfTransformation, [status(thm)], [f_211])).
% 18.70/10.46  tff(c_64, plain, (![A_38]: (m1_subset_1(k6_relat_1(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(cnfTransformation, [status(thm)], [f_187])).
% 18.70/10.46  tff(c_123, plain, (![A_38]: (m1_subset_1(k6_partfun1(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_64])).
% 18.70/10.46  tff(c_108, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_322])).
% 18.70/10.46  tff(c_1010, plain, (![D_121, C_122, A_123, B_124]: (D_121=C_122 | ~r2_relset_1(A_123, B_124, C_122, D_121) | ~m1_subset_1(D_121, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_185])).
% 18.70/10.46  tff(c_1024, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_108, c_1010])).
% 18.70/10.46  tff(c_1049, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_1024])).
% 18.70/10.46  tff(c_1109, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1049])).
% 18.70/10.46  tff(c_2097, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2090, c_1109])).
% 18.70/10.46  tff(c_2387, plain, (![C_187, A_185, D_188, F_189, E_190, B_186]: (m1_subset_1(k1_partfun1(A_185, B_186, C_187, D_188, E_190, F_189), k1_zfmisc_1(k2_zfmisc_1(A_185, D_188))) | ~m1_subset_1(F_189, k1_zfmisc_1(k2_zfmisc_1(C_187, D_188))) | ~v1_funct_1(F_189) | ~m1_subset_1(E_190, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))) | ~v1_funct_1(E_190))), inference(cnfTransformation, [status(thm)], [f_199])).
% 18.70/10.46  tff(c_2430, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2090, c_2387])).
% 18.70/10.46  tff(c_2454, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_118, c_116, c_112, c_2430])).
% 18.70/10.46  tff(c_2456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2097, c_2454])).
% 18.70/10.46  tff(c_2457, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1049])).
% 18.70/10.46  tff(c_9547, plain, (![A_481, B_480, D_482, F_485, C_483, E_484]: (k1_partfun1(A_481, B_480, C_483, D_482, E_484, F_485)=k5_relat_1(E_484, F_485) | ~m1_subset_1(F_485, k1_zfmisc_1(k2_zfmisc_1(C_483, D_482))) | ~v1_funct_1(F_485) | ~m1_subset_1(E_484, k1_zfmisc_1(k2_zfmisc_1(A_481, B_480))) | ~v1_funct_1(E_484))), inference(cnfTransformation, [status(thm)], [f_209])).
% 18.70/10.46  tff(c_9559, plain, (![A_481, B_480, E_484]: (k1_partfun1(A_481, B_480, '#skF_2', '#skF_1', E_484, '#skF_4')=k5_relat_1(E_484, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_484, k1_zfmisc_1(k2_zfmisc_1(A_481, B_480))) | ~v1_funct_1(E_484))), inference(resolution, [status(thm)], [c_112, c_9547])).
% 18.70/10.46  tff(c_10300, plain, (![A_519, B_520, E_521]: (k1_partfun1(A_519, B_520, '#skF_2', '#skF_1', E_521, '#skF_4')=k5_relat_1(E_521, '#skF_4') | ~m1_subset_1(E_521, k1_zfmisc_1(k2_zfmisc_1(A_519, B_520))) | ~v1_funct_1(E_521))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_9559])).
% 18.70/10.46  tff(c_10324, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_118, c_10300])).
% 18.70/10.46  tff(c_10342, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_2457, c_10324])).
% 18.70/10.46  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.70/10.46  tff(c_212, plain, (![B_85, A_86]: (v1_relat_1(B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_86)) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_32])).
% 18.70/10.46  tff(c_221, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_118, c_212])).
% 18.70/10.46  tff(c_230, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_221])).
% 18.70/10.46  tff(c_18, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_56])).
% 18.70/10.46  tff(c_131, plain, (![A_10]: (k2_relat_1(k6_partfun1(A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_18])).
% 18.70/10.46  tff(c_104, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_322])).
% 18.70/10.46  tff(c_114, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_322])).
% 18.70/10.46  tff(c_800, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_112, c_784])).
% 18.70/10.46  tff(c_2792, plain, (![C_199, A_200, B_201]: (v1_funct_1(k2_funct_1(C_199)) | k2_relset_1(A_200, B_201, C_199)!=B_201 | ~v2_funct_1(C_199) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))) | ~v1_funct_2(C_199, A_200, B_201) | ~v1_funct_1(C_199))), inference(cnfTransformation, [status(thm)], [f_270])).
% 18.70/10.46  tff(c_2807, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_112, c_2792])).
% 18.70/10.46  tff(c_2823, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relat_1('#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_114, c_800, c_2807])).
% 18.70/10.46  tff(c_2838, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2823])).
% 18.70/10.46  tff(c_120, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_322])).
% 18.70/10.46  tff(c_36, plain, (![A_16]: (v2_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 18.70/10.46  tff(c_125, plain, (![A_16]: (v2_funct_1(k6_partfun1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_36])).
% 18.70/10.46  tff(c_5912, plain, (![D_346, B_343, E_344, A_345, C_347]: (k1_xboole_0=C_347 | v2_funct_1(E_344) | k2_relset_1(A_345, B_343, D_346)!=B_343 | ~v2_funct_1(k1_partfun1(A_345, B_343, B_343, C_347, D_346, E_344)) | ~m1_subset_1(E_344, k1_zfmisc_1(k2_zfmisc_1(B_343, C_347))) | ~v1_funct_2(E_344, B_343, C_347) | ~v1_funct_1(E_344) | ~m1_subset_1(D_346, k1_zfmisc_1(k2_zfmisc_1(A_345, B_343))) | ~v1_funct_2(D_346, A_345, B_343) | ~v1_funct_1(D_346))), inference(cnfTransformation, [status(thm)], [f_254])).
% 18.70/10.46  tff(c_5919, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2457, c_5912])).
% 18.70/10.46  tff(c_5927, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_120, c_118, c_116, c_114, c_112, c_125, c_110, c_5919])).
% 18.70/10.46  tff(c_5929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2838, c_104, c_5927])).
% 18.70/10.46  tff(c_5930, plain, (k2_relat_1('#skF_4')!='#skF_1' | v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2823])).
% 18.70/10.46  tff(c_5983, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_5930])).
% 18.70/10.46  tff(c_658, plain, (![A_107, B_108, D_109]: (r2_relset_1(A_107, B_108, D_109, D_109) | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_185])).
% 18.70/10.46  tff(c_665, plain, (![A_38]: (r2_relset_1(A_38, A_38, k6_partfun1(A_38), k6_partfun1(A_38)))), inference(resolution, [status(thm)], [c_123, c_658])).
% 18.70/10.46  tff(c_7951, plain, (![A_421, B_422, C_423, D_424]: (k2_relset_1(A_421, B_422, C_423)=B_422 | ~r2_relset_1(B_422, B_422, k1_partfun1(B_422, A_421, A_421, B_422, D_424, C_423), k6_partfun1(B_422)) | ~m1_subset_1(D_424, k1_zfmisc_1(k2_zfmisc_1(B_422, A_421))) | ~v1_funct_2(D_424, B_422, A_421) | ~v1_funct_1(D_424) | ~m1_subset_1(C_423, k1_zfmisc_1(k2_zfmisc_1(A_421, B_422))) | ~v1_funct_2(C_423, A_421, B_422) | ~v1_funct_1(C_423))), inference(cnfTransformation, [status(thm)], [f_228])).
% 18.70/10.46  tff(c_7957, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2457, c_7951])).
% 18.70/10.46  tff(c_7961, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_114, c_112, c_122, c_120, c_118, c_665, c_800, c_7957])).
% 18.70/10.46  tff(c_7963, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5983, c_7961])).
% 18.70/10.46  tff(c_7965, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_5930])).
% 18.70/10.46  tff(c_7966, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7965, c_800])).
% 18.70/10.46  tff(c_5931, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2823])).
% 18.70/10.46  tff(c_9651, plain, (![A_489, C_490, B_491]: (k6_partfun1(A_489)=k5_relat_1(C_490, k2_funct_1(C_490)) | k1_xboole_0=B_491 | ~v2_funct_1(C_490) | k2_relset_1(A_489, B_491, C_490)!=B_491 | ~m1_subset_1(C_490, k1_zfmisc_1(k2_zfmisc_1(A_489, B_491))) | ~v1_funct_2(C_490, A_489, B_491) | ~v1_funct_1(C_490))), inference(cnfTransformation, [status(thm)], [f_286])).
% 18.70/10.46  tff(c_9663, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_112, c_9651])).
% 18.70/10.46  tff(c_9681, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_114, c_7966, c_5931, c_9663])).
% 18.70/10.46  tff(c_9682, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_104, c_9681])).
% 18.70/10.46  tff(c_218, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_112, c_212])).
% 18.70/10.46  tff(c_227, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_218])).
% 18.70/10.46  tff(c_96, plain, (![A_69]: (v1_funct_2(A_69, k1_relat_1(A_69), k2_relat_1(A_69)) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_296])).
% 18.70/10.46  tff(c_7985, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_1') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7965, c_96])).
% 18.70/10.46  tff(c_8005, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_116, c_7985])).
% 18.70/10.46  tff(c_94, plain, (![A_69]: (m1_subset_1(A_69, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_69), k2_relat_1(A_69)))) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_296])).
% 18.70/10.46  tff(c_797, plain, (![A_69]: (k2_relset_1(k1_relat_1(A_69), k2_relat_1(A_69), A_69)=k2_relat_1(A_69) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(resolution, [status(thm)], [c_94, c_784])).
% 18.70/10.46  tff(c_7976, plain, (k2_relset_1(k1_relat_1('#skF_4'), '#skF_1', '#skF_4')=k2_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7965, c_797])).
% 18.70/10.46  tff(c_7999, plain, (k2_relset_1(k1_relat_1('#skF_4'), '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_227, c_116, c_7965, c_7976])).
% 18.70/10.46  tff(c_7982, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_1'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7965, c_94])).
% 18.70/10.46  tff(c_8003, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_116, c_7982])).
% 18.70/10.46  tff(c_9657, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4')) | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1(k1_relat_1('#skF_4'), '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_8003, c_9651])).
% 18.70/10.46  tff(c_9673, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4')) | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_8005, c_7999, c_5931, c_9657])).
% 18.70/10.46  tff(c_9674, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_104, c_9673])).
% 18.70/10.46  tff(c_9733, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9682, c_9674])).
% 18.70/10.46  tff(c_9779, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9733, c_131])).
% 18.70/10.46  tff(c_9802, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_9779])).
% 18.70/10.46  tff(c_52, plain, (![A_24, B_26]: (k2_funct_1(A_24)=B_26 | k6_relat_1(k2_relat_1(A_24))!=k5_relat_1(B_26, A_24) | k2_relat_1(B_26)!=k1_relat_1(A_24) | ~v2_funct_1(A_24) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_150])).
% 18.70/10.46  tff(c_8132, plain, (![A_425, B_426]: (k2_funct_1(A_425)=B_426 | k6_partfun1(k2_relat_1(A_425))!=k5_relat_1(B_426, A_425) | k2_relat_1(B_426)!=k1_relat_1(A_425) | ~v2_funct_1(A_425) | ~v1_funct_1(B_426) | ~v1_relat_1(B_426) | ~v1_funct_1(A_425) | ~v1_relat_1(A_425))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_52])).
% 18.70/10.46  tff(c_8134, plain, (![B_426]: (k2_funct_1('#skF_4')=B_426 | k5_relat_1(B_426, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_426)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_426) | ~v1_relat_1(B_426) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7965, c_8132])).
% 18.70/10.46  tff(c_8166, plain, (![B_426]: (k2_funct_1('#skF_4')=B_426 | k5_relat_1(B_426, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_426)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_426) | ~v1_relat_1(B_426))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_116, c_5931, c_8134])).
% 18.70/10.46  tff(c_31574, plain, (![B_921]: (k2_funct_1('#skF_4')=B_921 | k5_relat_1(B_921, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_921)!='#skF_2' | ~v1_funct_1(B_921) | ~v1_relat_1(B_921))), inference(demodulation, [status(thm), theory('equality')], [c_9802, c_8166])).
% 18.70/10.46  tff(c_31742, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_230, c_31574])).
% 18.70/10.46  tff(c_31917, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_802, c_10342, c_31742])).
% 18.70/10.46  tff(c_28, plain, (![A_14]: (v1_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_80])).
% 18.70/10.46  tff(c_24, plain, (![A_13]: (k4_relat_1(A_13)=k2_funct_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_72])).
% 18.70/10.46  tff(c_5934, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_5931, c_24])).
% 18.70/10.46  tff(c_5937, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_116, c_5934])).
% 18.70/10.46  tff(c_6, plain, (![A_6]: (k4_relat_1(k4_relat_1(A_6))=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 18.70/10.46  tff(c_5965, plain, (k4_relat_1(k2_funct_1('#skF_4'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5937, c_6])).
% 18.70/10.46  tff(c_5981, plain, (k4_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_227, c_5965])).
% 18.70/10.46  tff(c_12, plain, (![A_9]: (k2_relat_1(k4_relat_1(A_9))=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 18.70/10.46  tff(c_5962, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5937, c_12])).
% 18.70/10.46  tff(c_5979, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_5962])).
% 18.70/10.46  tff(c_14, plain, (![A_9]: (k1_relat_1(k4_relat_1(A_9))=k2_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 18.70/10.46  tff(c_248, plain, (![A_88]: (k9_relat_1(A_88, k1_relat_1(A_88))=k2_relat_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_42])).
% 18.70/10.46  tff(c_257, plain, (![A_9]: (k9_relat_1(k4_relat_1(A_9), k2_relat_1(A_9))=k2_relat_1(k4_relat_1(A_9)) | ~v1_relat_1(k4_relat_1(A_9)) | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_14, c_248])).
% 18.70/10.46  tff(c_8396, plain, (k9_relat_1(k4_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'))=k2_relat_1(k4_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5979, c_257])).
% 18.70/10.46  tff(c_8428, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_5981, c_7965, c_5981, c_5981, c_8396])).
% 18.70/10.46  tff(c_9641, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_8428])).
% 18.70/10.46  tff(c_9644, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_9641])).
% 18.70/10.46  tff(c_9648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_227, c_116, c_9644])).
% 18.70/10.46  tff(c_9650, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_8428])).
% 18.70/10.46  tff(c_7964, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5930])).
% 18.70/10.46  tff(c_38, plain, (![A_17]: (v2_funct_1(k2_funct_1(A_17)) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_100])).
% 18.70/10.46  tff(c_102, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_322])).
% 18.70/10.46  tff(c_8474, plain, (![C_430, B_431, A_432]: (v1_funct_2(k2_funct_1(C_430), B_431, A_432) | k2_relset_1(A_432, B_431, C_430)!=B_431 | ~v2_funct_1(C_430) | ~m1_subset_1(C_430, k1_zfmisc_1(k2_zfmisc_1(A_432, B_431))) | ~v1_funct_2(C_430, A_432, B_431) | ~v1_funct_1(C_430))), inference(cnfTransformation, [status(thm)], [f_270])).
% 18.70/10.46  tff(c_8492, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', '#skF_2') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_112, c_8474])).
% 18.70/10.46  tff(c_8511, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_114, c_5931, c_7966, c_8492])).
% 18.70/10.46  tff(c_9814, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9802, c_5979])).
% 18.70/10.46  tff(c_5959, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5937, c_14])).
% 18.70/10.46  tff(c_5977, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_5959])).
% 18.70/10.46  tff(c_8337, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7965, c_5977])).
% 18.70/10.46  tff(c_9912, plain, (k2_relset_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2', k2_funct_1('#skF_4'))=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9814, c_797])).
% 18.70/10.46  tff(c_9943, plain, (k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9650, c_7964, c_9814, c_8337, c_9912])).
% 18.70/10.46  tff(c_9918, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9814, c_94])).
% 18.70/10.46  tff(c_9947, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_9650, c_7964, c_8337, c_9918])).
% 18.70/10.46  tff(c_92, plain, (![A_66, C_68, B_67]: (k6_partfun1(A_66)=k5_relat_1(C_68, k2_funct_1(C_68)) | k1_xboole_0=B_67 | ~v2_funct_1(C_68) | k2_relset_1(A_66, B_67, C_68)!=B_67 | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~v1_funct_2(C_68, A_66, B_67) | ~v1_funct_1(C_68))), inference(cnfTransformation, [status(thm)], [f_286])).
% 18.70/10.46  tff(c_10112, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))!='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_9947, c_92])).
% 18.70/10.46  tff(c_10143, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7964, c_8511, c_9943, c_10112])).
% 18.70/10.46  tff(c_10144, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_102, c_10143])).
% 18.70/10.46  tff(c_10167, plain, (~v2_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_10144])).
% 18.70/10.46  tff(c_10170, plain, (~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_10167])).
% 18.70/10.46  tff(c_10174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_227, c_116, c_5931, c_10170])).
% 18.70/10.46  tff(c_10176, plain, (v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_10144])).
% 18.70/10.46  tff(c_10179, plain, (k4_relat_1(k2_funct_1('#skF_4'))=k2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_10176, c_24])).
% 18.70/10.46  tff(c_10182, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9650, c_7964, c_5981, c_10179])).
% 18.70/10.46  tff(c_31970, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_31917, c_10182])).
% 18.70/10.46  tff(c_32011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_31970])).
% 18.70/10.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.70/10.46  
% 18.70/10.46  Inference rules
% 18.70/10.46  ----------------------
% 18.70/10.46  #Ref     : 0
% 18.70/10.46  #Sup     : 6742
% 18.70/10.46  #Fact    : 0
% 18.70/10.46  #Define  : 0
% 18.70/10.46  #Split   : 53
% 18.70/10.46  #Chain   : 0
% 18.70/10.46  #Close   : 0
% 18.70/10.46  
% 18.70/10.46  Ordering : KBO
% 18.70/10.46  
% 18.70/10.46  Simplification rules
% 18.70/10.46  ----------------------
% 18.70/10.46  #Subsume      : 356
% 18.70/10.46  #Demod        : 20710
% 18.70/10.46  #Tautology    : 2811
% 18.70/10.46  #SimpNegUnit  : 315
% 18.70/10.46  #BackRed      : 371
% 18.70/10.46  
% 18.70/10.46  #Partial instantiations: 0
% 18.70/10.46  #Strategies tried      : 1
% 18.70/10.46  
% 18.70/10.46  Timing (in seconds)
% 18.70/10.46  ----------------------
% 18.70/10.46  Preprocessing        : 0.43
% 18.70/10.46  Parsing              : 0.22
% 18.70/10.46  CNF conversion       : 0.03
% 18.70/10.46  Main loop            : 9.24
% 18.70/10.46  Inferencing          : 1.45
% 18.70/10.46  Reduction            : 5.88
% 18.70/10.46  Demodulation         : 5.30
% 18.70/10.46  BG Simplification    : 0.15
% 18.70/10.46  Subsumption          : 1.40
% 18.70/10.46  Abstraction          : 0.24
% 18.70/10.46  MUC search           : 0.00
% 18.70/10.46  Cooper               : 0.00
% 18.70/10.46  Total                : 9.72
% 18.70/10.46  Index Insertion      : 0.00
% 18.70/10.46  Index Deletion       : 0.00
% 18.70/10.46  Index Matching       : 0.00
% 18.70/10.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
