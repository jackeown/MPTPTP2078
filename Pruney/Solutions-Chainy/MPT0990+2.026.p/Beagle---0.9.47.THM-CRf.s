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
% DateTime   : Thu Dec  3 10:12:59 EST 2020

% Result     : Theorem 14.15s
% Output     : CNFRefutation 14.51s
% Verified   : 
% Statistics : Number of formulae       :  354 (129910 expanded)
%              Number of leaves         :   52 (44527 expanded)
%              Depth                    :   40
%              Number of atoms          :  925 (518025 expanded)
%              Number of equality atoms :  288 (188100 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_257,negated_conjecture,(
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

tff(f_138,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_170,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_172,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_148,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_146,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_160,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_134,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_231,axiom,(
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

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_105,axiom,(
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

tff(f_189,axiom,(
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

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_215,axiom,(
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

tff(f_113,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_130,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_128,axiom,(
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

tff(c_78,plain,(
    k2_funct_1('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_100,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_88,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_96,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_313,plain,(
    ! [A_87,B_88,C_89] :
      ( k2_relset_1(A_87,B_88,C_89) = k2_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_319,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_313])).

tff(c_326,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_319])).

tff(c_94,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_90,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_1943,plain,(
    ! [A_202,C_206,B_203,D_207,F_205,E_204] :
      ( k1_partfun1(A_202,B_203,C_206,D_207,E_204,F_205) = k5_relat_1(E_204,F_205)
      | ~ m1_subset_1(F_205,k1_zfmisc_1(k2_zfmisc_1(C_206,D_207)))
      | ~ v1_funct_1(F_205)
      | ~ m1_subset_1(E_204,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203)))
      | ~ v1_funct_1(E_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1949,plain,(
    ! [A_202,B_203,E_204] :
      ( k1_partfun1(A_202,B_203,'#skF_3','#skF_2',E_204,'#skF_5') = k5_relat_1(E_204,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_204,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203)))
      | ~ v1_funct_1(E_204) ) ),
    inference(resolution,[status(thm)],[c_90,c_1943])).

tff(c_2070,plain,(
    ! [A_219,B_220,E_221] :
      ( k1_partfun1(A_219,B_220,'#skF_3','#skF_2',E_221,'#skF_5') = k5_relat_1(E_221,'#skF_5')
      | ~ m1_subset_1(E_221,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220)))
      | ~ v1_funct_1(E_221) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1949])).

tff(c_2076,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_2070])).

tff(c_2083,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2076])).

tff(c_62,plain,(
    ! [A_44] : k6_relat_1(A_44) = k6_partfun1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_54,plain,(
    ! [A_31] : m1_subset_1(k6_relat_1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_101,plain,(
    ! [A_31] : m1_subset_1(k6_partfun1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_54])).

tff(c_86,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_581,plain,(
    ! [D_106,C_107,A_108,B_109] :
      ( D_106 = C_107
      | ~ r2_relset_1(A_108,B_109,C_107,D_106)
      | ~ m1_subset_1(D_106,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_589,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_86,c_581])).

tff(c_604,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_589])).

tff(c_1833,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_604])).

tff(c_2088,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2083,c_1833])).

tff(c_2228,plain,(
    ! [B_226,A_229,C_228,F_227,D_230,E_225] :
      ( m1_subset_1(k1_partfun1(A_229,B_226,C_228,D_230,E_225,F_227),k1_zfmisc_1(k2_zfmisc_1(A_229,D_230)))
      | ~ m1_subset_1(F_227,k1_zfmisc_1(k2_zfmisc_1(C_228,D_230)))
      | ~ v1_funct_1(F_227)
      | ~ m1_subset_1(E_225,k1_zfmisc_1(k2_zfmisc_1(A_229,B_226)))
      | ~ v1_funct_1(E_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_2262,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2083,c_2228])).

tff(c_2283,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_96,c_94,c_90,c_2262])).

tff(c_2285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2088,c_2283])).

tff(c_2286,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_604])).

tff(c_9080,plain,(
    ! [A_566,D_571,F_569,B_567,C_570,E_568] :
      ( k1_partfun1(A_566,B_567,C_570,D_571,E_568,F_569) = k5_relat_1(E_568,F_569)
      | ~ m1_subset_1(F_569,k1_zfmisc_1(k2_zfmisc_1(C_570,D_571)))
      | ~ v1_funct_1(F_569)
      | ~ m1_subset_1(E_568,k1_zfmisc_1(k2_zfmisc_1(A_566,B_567)))
      | ~ v1_funct_1(E_568) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_9086,plain,(
    ! [A_566,B_567,E_568] :
      ( k1_partfun1(A_566,B_567,'#skF_3','#skF_2',E_568,'#skF_5') = k5_relat_1(E_568,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_568,k1_zfmisc_1(k2_zfmisc_1(A_566,B_567)))
      | ~ v1_funct_1(E_568) ) ),
    inference(resolution,[status(thm)],[c_90,c_9080])).

tff(c_11429,plain,(
    ! [A_677,B_678,E_679] :
      ( k1_partfun1(A_677,B_678,'#skF_3','#skF_2',E_679,'#skF_5') = k5_relat_1(E_679,'#skF_5')
      | ~ m1_subset_1(E_679,k1_zfmisc_1(k2_zfmisc_1(A_677,B_678)))
      | ~ v1_funct_1(E_679) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_9086])).

tff(c_11441,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_11429])).

tff(c_11452,plain,(
    k5_relat_1('#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2286,c_11441])).

tff(c_184,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_196,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_184])).

tff(c_197,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_184])).

tff(c_22,plain,(
    ! [A_9] :
      ( v1_relat_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_84,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_275,plain,(
    ! [A_84] :
      ( k1_relat_1(k2_funct_1(A_84)) = k2_relat_1(A_84)
      | ~ v2_funct_1(A_84)
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_18,plain,(
    ! [A_8] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_8)),A_8) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_106,plain,(
    ! [A_8] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_8)),A_8) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_18])).

tff(c_479,plain,(
    ! [A_100] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_100)),k2_funct_1(A_100)) = k2_funct_1(A_100)
      | ~ v1_relat_1(k2_funct_1(A_100))
      | ~ v2_funct_1(A_100)
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_106])).

tff(c_503,plain,
    ( k5_relat_1(k6_partfun1('#skF_3'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_479])).

tff(c_520,plain,
    ( k5_relat_1(k6_partfun1('#skF_3'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_100,c_84,c_503])).

tff(c_525,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_520])).

tff(c_552,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_525])).

tff(c_556,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_100,c_552])).

tff(c_558,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_520])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_7] : k2_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_107,plain,(
    ! [A_7] : k2_relat_1(k6_partfun1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_16])).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_113,plain,(
    ! [A_63] :
      ( k1_xboole_0 = A_63
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_117,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_113])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_119,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_80])).

tff(c_98,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_76,plain,(
    ! [A_56,C_58,B_57] :
      ( k6_partfun1(A_56) = k5_relat_1(C_58,k2_funct_1(C_58))
      | k1_xboole_0 = B_57
      | ~ v2_funct_1(C_58)
      | k2_relset_1(A_56,B_57,C_58) != B_57
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ v1_funct_2(C_58,A_56,B_57)
      | ~ v1_funct_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_929,plain,(
    ! [A_148,C_149,B_150] :
      ( k6_partfun1(A_148) = k5_relat_1(C_149,k2_funct_1(C_149))
      | B_150 = '#skF_1'
      | ~ v2_funct_1(C_149)
      | k2_relset_1(A_148,B_150,C_149) != B_150
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_148,B_150)))
      | ~ v1_funct_2(C_149,A_148,B_150)
      | ~ v1_funct_1(C_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_76])).

tff(c_933,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_929])).

tff(c_941,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_88,c_84,c_933])).

tff(c_942,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_941])).

tff(c_36,plain,(
    ! [A_12] :
      ( k1_relat_1(k2_funct_1(A_12)) = k2_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_341,plain,(
    ! [B_91,A_92] :
      ( k2_relat_1(k5_relat_1(B_91,A_92)) = k2_relat_1(A_92)
      | ~ r1_tarski(k1_relat_1(A_92),k2_relat_1(B_91))
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_344,plain,(
    ! [A_92] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_92)) = k2_relat_1(A_92)
      | ~ r1_tarski(k1_relat_1(A_92),'#skF_3')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_341])).

tff(c_390,plain,(
    ! [A_95] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_95)) = k2_relat_1(A_95)
      | ~ r1_tarski(k1_relat_1(A_95),'#skF_3')
      | ~ v1_relat_1(A_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_344])).

tff(c_393,plain,(
    ! [A_12] :
      ( k2_relat_1(k5_relat_1('#skF_4',k2_funct_1(A_12))) = k2_relat_1(k2_funct_1(A_12))
      | ~ r1_tarski(k2_relat_1(A_12),'#skF_3')
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_390])).

tff(c_950,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_942,c_393])).

tff(c_954,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_100,c_84,c_558,c_10,c_326,c_107,c_950])).

tff(c_34,plain,(
    ! [A_12] :
      ( k2_relat_1(k2_funct_1(A_12)) = k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_970,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_954,c_34])).

tff(c_985,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_100,c_84,c_970])).

tff(c_38,plain,(
    ! [A_13,B_15] :
      ( k2_funct_1(A_13) = B_15
      | k6_relat_1(k2_relat_1(A_13)) != k5_relat_1(B_15,A_13)
      | k2_relat_1(B_15) != k1_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_676,plain,(
    ! [A_114,B_115] :
      ( k2_funct_1(A_114) = B_115
      | k6_partfun1(k2_relat_1(A_114)) != k5_relat_1(B_115,A_114)
      | k2_relat_1(B_115) != k1_relat_1(A_114)
      | ~ v2_funct_1(A_114)
      | ~ v1_funct_1(B_115)
      | ~ v1_relat_1(B_115)
      | ~ v1_funct_1(A_114)
      | ~ v1_relat_1(A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_38])).

tff(c_694,plain,(
    ! [B_115] :
      ( k2_funct_1('#skF_4') = B_115
      | k5_relat_1(B_115,'#skF_4') != k6_partfun1('#skF_3')
      | k2_relat_1(B_115) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_115)
      | ~ v1_relat_1(B_115)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_676])).

tff(c_717,plain,(
    ! [B_116] :
      ( k2_funct_1('#skF_4') = B_116
      | k5_relat_1(B_116,'#skF_4') != k6_partfun1('#skF_3')
      | k2_relat_1(B_116) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_116)
      | ~ v1_relat_1(B_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_100,c_84,c_694])).

tff(c_723,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k5_relat_1('#skF_5','#skF_4') != k6_partfun1('#skF_3')
    | k2_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_197,c_717])).

tff(c_737,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k5_relat_1('#skF_5','#skF_4') != k6_partfun1('#skF_3')
    | k2_relat_1('#skF_5') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_723])).

tff(c_738,plain,
    ( k5_relat_1('#skF_5','#skF_4') != k6_partfun1('#skF_3')
    | k2_relat_1('#skF_5') != k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_737])).

tff(c_745,plain,(
    k2_relat_1('#skF_5') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_738])).

tff(c_991,plain,(
    k2_relat_1('#skF_5') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_745])).

tff(c_92,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_265,plain,(
    ! [A_81,B_82,D_83] :
      ( r2_relset_1(A_81,B_82,D_83,D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_272,plain,(
    ! [A_31] : r2_relset_1(A_31,A_31,k6_partfun1(A_31),k6_partfun1(A_31)) ),
    inference(resolution,[status(thm)],[c_101,c_265])).

tff(c_327,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_313])).

tff(c_863,plain,(
    ! [F_138,B_136,E_137,C_139,D_140,A_135] :
      ( k1_partfun1(A_135,B_136,C_139,D_140,E_137,F_138) = k5_relat_1(E_137,F_138)
      | ~ m1_subset_1(F_138,k1_zfmisc_1(k2_zfmisc_1(C_139,D_140)))
      | ~ v1_funct_1(F_138)
      | ~ m1_subset_1(E_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136)))
      | ~ v1_funct_1(E_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_869,plain,(
    ! [A_135,B_136,E_137] :
      ( k1_partfun1(A_135,B_136,'#skF_3','#skF_2',E_137,'#skF_5') = k5_relat_1(E_137,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136)))
      | ~ v1_funct_1(E_137) ) ),
    inference(resolution,[status(thm)],[c_90,c_863])).

tff(c_905,plain,(
    ! [A_145,B_146,E_147] :
      ( k1_partfun1(A_145,B_146,'#skF_3','#skF_2',E_147,'#skF_5') = k5_relat_1(E_147,'#skF_5')
      | ~ m1_subset_1(E_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ v1_funct_1(E_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_869])).

tff(c_911,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_905])).

tff(c_918,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_911])).

tff(c_1304,plain,(
    ! [F_163,D_166,A_165,C_164,B_162,E_161] :
      ( m1_subset_1(k1_partfun1(A_165,B_162,C_164,D_166,E_161,F_163),k1_zfmisc_1(k2_zfmisc_1(A_165,D_166)))
      | ~ m1_subset_1(F_163,k1_zfmisc_1(k2_zfmisc_1(C_164,D_166)))
      | ~ v1_funct_1(F_163)
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(A_165,B_162)))
      | ~ v1_funct_1(E_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1341,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_918,c_1304])).

tff(c_1364,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_96,c_94,c_90,c_1341])).

tff(c_1484,plain,(
    k5_relat_1('#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1364,c_918,c_918,c_604])).

tff(c_1488,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1484,c_918])).

tff(c_1797,plain,(
    ! [A_183,B_184,C_185,D_186] :
      ( k2_relset_1(A_183,B_184,C_185) = B_184
      | ~ r2_relset_1(B_184,B_184,k1_partfun1(B_184,A_183,A_183,B_184,D_186,C_185),k6_partfun1(B_184))
      | ~ m1_subset_1(D_186,k1_zfmisc_1(k2_zfmisc_1(B_184,A_183)))
      | ~ v1_funct_2(D_186,B_184,A_183)
      | ~ v1_funct_1(D_186)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ v1_funct_2(C_185,A_183,B_184)
      | ~ v1_funct_1(C_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_1800,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1488,c_1797])).

tff(c_1805,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_90,c_100,c_98,c_96,c_272,c_327,c_1800])).

tff(c_1807,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_991,c_1805])).

tff(c_1809,plain,(
    k2_relat_1('#skF_5') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_738])).

tff(c_281,plain,(
    ! [A_84] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_84)),k2_funct_1(A_84)) = k2_funct_1(A_84)
      | ~ v1_relat_1(k2_funct_1(A_84))
      | ~ v2_funct_1(A_84)
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_106])).

tff(c_1816,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k2_funct_1('#skF_5')) = k2_funct_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1809,c_281])).

tff(c_1825,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k2_funct_1('#skF_5')) = k2_funct_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_94,c_1816])).

tff(c_2296,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1825])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_120,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_82])).

tff(c_26,plain,(
    ! [A_10] : v2_funct_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_104,plain,(
    ! [A_10] : v2_funct_1(k6_partfun1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_26])).

tff(c_68,plain,(
    ! [A_50,E_55,B_51,C_52,D_53] :
      ( k1_xboole_0 = C_52
      | v2_funct_1(E_55)
      | k2_relset_1(A_50,B_51,D_53) != B_51
      | ~ v2_funct_1(k1_partfun1(A_50,B_51,B_51,C_52,D_53,E_55))
      | ~ m1_subset_1(E_55,k1_zfmisc_1(k2_zfmisc_1(B_51,C_52)))
      | ~ v1_funct_2(E_55,B_51,C_52)
      | ~ v1_funct_1(E_55)
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ v1_funct_2(D_53,A_50,B_51)
      | ~ v1_funct_1(D_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_3222,plain,(
    ! [C_296,A_294,B_297,D_298,E_295] :
      ( C_296 = '#skF_1'
      | v2_funct_1(E_295)
      | k2_relset_1(A_294,B_297,D_298) != B_297
      | ~ v2_funct_1(k1_partfun1(A_294,B_297,B_297,C_296,D_298,E_295))
      | ~ m1_subset_1(E_295,k1_zfmisc_1(k2_zfmisc_1(B_297,C_296)))
      | ~ v1_funct_2(E_295,B_297,C_296)
      | ~ v1_funct_1(E_295)
      | ~ m1_subset_1(D_298,k1_zfmisc_1(k2_zfmisc_1(A_294,B_297)))
      | ~ v1_funct_2(D_298,A_294,B_297)
      | ~ v1_funct_1(D_298) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_68])).

tff(c_3226,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_2286,c_3222])).

tff(c_3231,plain,
    ( '#skF_2' = '#skF_1'
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_96,c_94,c_92,c_90,c_104,c_88,c_3226])).

tff(c_3233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2296,c_120,c_3231])).

tff(c_3234,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_5'))
    | k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k2_funct_1('#skF_5')) = k2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1825])).

tff(c_3236,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3234])).

tff(c_3239,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_3236])).

tff(c_3243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_94,c_3239])).

tff(c_3245,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3234])).

tff(c_3235,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1825])).

tff(c_40,plain,(
    ! [A_16] :
      ( k2_funct_1(k2_funct_1(A_16)) = A_16
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_28,plain,(
    ! [A_11] :
      ( v2_funct_1(k2_funct_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    ! [A_9] :
      ( v1_funct_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_105,plain,(
    ! [A_10] : v1_relat_1(k6_partfun1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_24])).

tff(c_3635,plain,(
    ! [A_341,B_338,F_339,C_340,E_337,D_342] :
      ( v1_funct_1(k1_partfun1(A_341,B_338,C_340,D_342,E_337,F_339))
      | ~ m1_subset_1(F_339,k1_zfmisc_1(k2_zfmisc_1(C_340,D_342)))
      | ~ v1_funct_1(F_339)
      | ~ m1_subset_1(E_337,k1_zfmisc_1(k2_zfmisc_1(A_341,B_338)))
      | ~ v1_funct_1(E_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_3641,plain,(
    ! [A_341,B_338,E_337] :
      ( v1_funct_1(k1_partfun1(A_341,B_338,'#skF_3','#skF_2',E_337,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_337,k1_zfmisc_1(k2_zfmisc_1(A_341,B_338)))
      | ~ v1_funct_1(E_337) ) ),
    inference(resolution,[status(thm)],[c_90,c_3635])).

tff(c_6202,plain,(
    ! [A_463,B_464,E_465] :
      ( v1_funct_1(k1_partfun1(A_463,B_464,'#skF_3','#skF_2',E_465,'#skF_5'))
      | ~ m1_subset_1(E_465,k1_zfmisc_1(k2_zfmisc_1(A_463,B_464)))
      | ~ v1_funct_1(E_465) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_3641])).

tff(c_6208,plain,
    ( v1_funct_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_6202])).

tff(c_6215,plain,(
    v1_funct_1(k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2286,c_6208])).

tff(c_44,plain,(
    ! [A_20] : k2_funct_1(k6_relat_1(A_20)) = k6_relat_1(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_102,plain,(
    ! [A_20] : k2_funct_1(k6_partfun1(A_20)) = k6_partfun1(A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_44])).

tff(c_6236,plain,(
    ! [A_468,C_469,B_470] :
      ( k6_partfun1(A_468) = k5_relat_1(C_469,k2_funct_1(C_469))
      | B_470 = '#skF_1'
      | ~ v2_funct_1(C_469)
      | k2_relset_1(A_468,B_470,C_469) != B_470
      | ~ m1_subset_1(C_469,k1_zfmisc_1(k2_zfmisc_1(A_468,B_470)))
      | ~ v1_funct_2(C_469,A_468,B_470)
      | ~ v1_funct_1(C_469) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_76])).

tff(c_6240,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_6236])).

tff(c_6248,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_88,c_84,c_6240])).

tff(c_6249,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_6248])).

tff(c_6257,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6249,c_393])).

tff(c_6261,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_100,c_84,c_558,c_10,c_326,c_107,c_6257])).

tff(c_6277,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6261,c_34])).

tff(c_6292,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_100,c_84,c_6277])).

tff(c_3244,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k2_funct_1('#skF_5')) = k2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_3234])).

tff(c_6304,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_5')) = k2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6292,c_3244])).

tff(c_605,plain,(
    ! [B_110,A_111] :
      ( k5_relat_1(k2_funct_1(B_110),k2_funct_1(A_111)) = k2_funct_1(k5_relat_1(A_111,B_110))
      | ~ v2_funct_1(B_110)
      | ~ v2_funct_1(A_111)
      | ~ v1_funct_1(B_110)
      | ~ v1_relat_1(B_110)
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_8534,plain,(
    ! [A_551,A_552] :
      ( k2_funct_1(k5_relat_1(A_551,k2_funct_1(A_552))) = k5_relat_1(A_552,k2_funct_1(A_551))
      | ~ v2_funct_1(k2_funct_1(A_552))
      | ~ v2_funct_1(A_551)
      | ~ v1_funct_1(k2_funct_1(A_552))
      | ~ v1_relat_1(k2_funct_1(A_552))
      | ~ v1_funct_1(A_551)
      | ~ v1_relat_1(A_551)
      | ~ v2_funct_1(A_552)
      | ~ v1_funct_1(A_552)
      | ~ v1_relat_1(A_552) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_605])).

tff(c_8591,plain,
    ( k5_relat_1('#skF_5',k2_funct_1(k6_partfun1('#skF_2'))) = k2_funct_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v1_funct_1(k6_partfun1('#skF_2'))
    | ~ v1_relat_1(k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6304,c_8534])).

tff(c_8625,plain,
    ( k5_relat_1('#skF_5',k6_partfun1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_94,c_3235,c_105,c_6215,c_3245,c_104,c_102,c_8591])).

tff(c_8917,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_8625])).

tff(c_8920,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_8917])).

tff(c_8924,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_94,c_8920])).

tff(c_8925,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_5'))
    | k5_relat_1('#skF_5',k6_partfun1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_8625])).

tff(c_9032,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_8925])).

tff(c_9035,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_9032])).

tff(c_9039,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_94,c_3235,c_9035])).

tff(c_9040,plain,(
    k5_relat_1('#skF_5',k6_partfun1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_8925])).

tff(c_3668,plain,(
    ! [A_347,B_348,E_349] :
      ( v1_funct_1(k1_partfun1(A_347,B_348,'#skF_3','#skF_2',E_349,'#skF_5'))
      | ~ m1_subset_1(E_349,k1_zfmisc_1(k2_zfmisc_1(A_347,B_348)))
      | ~ v1_funct_1(E_349) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_3641])).

tff(c_3674,plain,
    ( v1_funct_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_3668])).

tff(c_3681,plain,(
    v1_funct_1(k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2286,c_3674])).

tff(c_1810,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1809,c_327])).

tff(c_3743,plain,(
    ! [A_361,C_362,B_363] :
      ( k6_partfun1(A_361) = k5_relat_1(C_362,k2_funct_1(C_362))
      | B_363 = '#skF_1'
      | ~ v2_funct_1(C_362)
      | k2_relset_1(A_361,B_363,C_362) != B_363
      | ~ m1_subset_1(C_362,k1_zfmisc_1(k2_zfmisc_1(A_361,B_363)))
      | ~ v1_funct_2(C_362,A_361,B_363)
      | ~ v1_funct_1(C_362) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_76])).

tff(c_3749,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_2','#skF_5') != '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_3743])).

tff(c_3759,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | '#skF_2' = '#skF_1'
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_1810,c_3235,c_3749])).

tff(c_3760,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_3759])).

tff(c_3803,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3760])).

tff(c_3747,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_3743])).

tff(c_3755,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_88,c_84,c_3747])).

tff(c_3756,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_3755])).

tff(c_3764,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3756,c_393])).

tff(c_3768,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_100,c_84,c_558,c_10,c_326,c_107,c_3764])).

tff(c_3784,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3768,c_34])).

tff(c_3799,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_100,c_84,c_3784])).

tff(c_3804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3803,c_3799])).

tff(c_3806,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3760])).

tff(c_3814,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_5')) = k2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3806,c_3244])).

tff(c_5706,plain,(
    ! [A_439,A_440] :
      ( k2_funct_1(k5_relat_1(A_439,k2_funct_1(A_440))) = k5_relat_1(A_440,k2_funct_1(A_439))
      | ~ v2_funct_1(k2_funct_1(A_440))
      | ~ v2_funct_1(A_439)
      | ~ v1_funct_1(k2_funct_1(A_440))
      | ~ v1_relat_1(k2_funct_1(A_440))
      | ~ v1_funct_1(A_439)
      | ~ v1_relat_1(A_439)
      | ~ v2_funct_1(A_440)
      | ~ v1_funct_1(A_440)
      | ~ v1_relat_1(A_440) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_605])).

tff(c_5763,plain,
    ( k5_relat_1('#skF_5',k2_funct_1(k6_partfun1('#skF_2'))) = k2_funct_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v1_funct_1(k6_partfun1('#skF_2'))
    | ~ v1_relat_1(k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3814,c_5706])).

tff(c_5797,plain,
    ( k5_relat_1('#skF_5',k6_partfun1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_94,c_3235,c_105,c_3681,c_3245,c_104,c_102,c_5763])).

tff(c_5999,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_5797])).

tff(c_6002,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_5999])).

tff(c_6006,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_94,c_6002])).

tff(c_6007,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_5'))
    | k5_relat_1('#skF_5',k6_partfun1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_5797])).

tff(c_6009,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6007])).

tff(c_6012,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_6009])).

tff(c_6016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_94,c_3235,c_6012])).

tff(c_6017,plain,(
    k5_relat_1('#skF_5',k6_partfun1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6007])).

tff(c_3333,plain,(
    ! [E_301,B_302,D_306,C_304,F_303,A_305] :
      ( v1_funct_1(k1_partfun1(A_305,B_302,C_304,D_306,E_301,F_303))
      | ~ m1_subset_1(F_303,k1_zfmisc_1(k2_zfmisc_1(C_304,D_306)))
      | ~ v1_funct_1(F_303)
      | ~ m1_subset_1(E_301,k1_zfmisc_1(k2_zfmisc_1(A_305,B_302)))
      | ~ v1_funct_1(E_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_3339,plain,(
    ! [A_305,B_302,E_301] :
      ( v1_funct_1(k1_partfun1(A_305,B_302,'#skF_3','#skF_2',E_301,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_301,k1_zfmisc_1(k2_zfmisc_1(A_305,B_302)))
      | ~ v1_funct_1(E_301) ) ),
    inference(resolution,[status(thm)],[c_90,c_3333])).

tff(c_3365,plain,(
    ! [A_311,B_312,E_313] :
      ( v1_funct_1(k1_partfun1(A_311,B_312,'#skF_3','#skF_2',E_313,'#skF_5'))
      | ~ m1_subset_1(E_313,k1_zfmisc_1(k2_zfmisc_1(A_311,B_312)))
      | ~ v1_funct_1(E_313) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_3339])).

tff(c_3371,plain,
    ( v1_funct_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_3365])).

tff(c_3378,plain,(
    v1_funct_1(k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2286,c_3371])).

tff(c_732,plain,(
    ! [A_10] :
      ( k6_partfun1(A_10) = k2_funct_1('#skF_4')
      | k5_relat_1(k6_partfun1(A_10),'#skF_4') != k6_partfun1('#skF_3')
      | k2_relat_1(k6_partfun1(A_10)) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(k6_partfun1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_105,c_717])).

tff(c_3397,plain,(
    ! [A_321] :
      ( k6_partfun1(A_321) = k2_funct_1('#skF_4')
      | k5_relat_1(k6_partfun1(A_321),'#skF_4') != k6_partfun1('#skF_3')
      | k1_relat_1('#skF_4') != A_321
      | ~ v1_funct_1(k6_partfun1(A_321)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_732])).

tff(c_3401,plain,
    ( k6_partfun1('#skF_2') = k2_funct_1('#skF_4')
    | k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') != k6_partfun1('#skF_3')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_3378,c_3397])).

tff(c_3402,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3401])).

tff(c_3502,plain,(
    ! [A_333,C_334,B_335] :
      ( k6_partfun1(A_333) = k5_relat_1(C_334,k2_funct_1(C_334))
      | B_335 = '#skF_1'
      | ~ v2_funct_1(C_334)
      | k2_relset_1(A_333,B_335,C_334) != B_335
      | ~ m1_subset_1(C_334,k1_zfmisc_1(k2_zfmisc_1(A_333,B_335)))
      | ~ v1_funct_2(C_334,A_333,B_335)
      | ~ v1_funct_1(C_334) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_76])).

tff(c_3506,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_3502])).

tff(c_3514,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_88,c_84,c_3506])).

tff(c_3515,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_3514])).

tff(c_3523,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3515,c_393])).

tff(c_3527,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_100,c_84,c_558,c_10,c_326,c_107,c_3523])).

tff(c_3543,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3527,c_34])).

tff(c_3558,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_100,c_84,c_3543])).

tff(c_3560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3402,c_3558])).

tff(c_3562,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3401])).

tff(c_620,plain,(
    ! [A_20,A_111] :
      ( k5_relat_1(k6_partfun1(A_20),k2_funct_1(A_111)) = k2_funct_1(k5_relat_1(A_111,k6_partfun1(A_20)))
      | ~ v2_funct_1(k6_partfun1(A_20))
      | ~ v2_funct_1(A_111)
      | ~ v1_funct_1(k6_partfun1(A_20))
      | ~ v1_relat_1(k6_partfun1(A_20))
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_605])).

tff(c_627,plain,(
    ! [A_20,A_111] :
      ( k5_relat_1(k6_partfun1(A_20),k2_funct_1(A_111)) = k2_funct_1(k5_relat_1(A_111,k6_partfun1(A_20)))
      | ~ v2_funct_1(A_111)
      | ~ v1_funct_1(k6_partfun1(A_20))
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_104,c_620])).

tff(c_3283,plain,
    ( k2_funct_1(k5_relat_1('#skF_5',k6_partfun1(k1_relat_1('#skF_4')))) = k2_funct_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1(k6_partfun1(k1_relat_1('#skF_4')))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3244,c_627])).

tff(c_3295,plain,
    ( k2_funct_1(k5_relat_1('#skF_5',k6_partfun1(k1_relat_1('#skF_4')))) = k2_funct_1('#skF_5')
    | ~ v1_funct_1(k6_partfun1(k1_relat_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_94,c_3235,c_3283])).

tff(c_3332,plain,(
    ~ v1_funct_1(k6_partfun1(k1_relat_1('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_3295])).

tff(c_3564,plain,(
    ~ v1_funct_1(k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3562,c_3332])).

tff(c_3574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3378,c_3564])).

tff(c_3575,plain,(
    k2_funct_1(k5_relat_1('#skF_5',k6_partfun1(k1_relat_1('#skF_4')))) = k2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_3295])).

tff(c_3618,plain,
    ( v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_funct_1(k5_relat_1('#skF_5',k6_partfun1(k1_relat_1('#skF_4'))))
    | ~ v1_relat_1(k5_relat_1('#skF_5',k6_partfun1(k1_relat_1('#skF_4')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3575,c_20])).

tff(c_3649,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_5',k6_partfun1(k1_relat_1('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_3618])).

tff(c_3809,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_5',k6_partfun1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3806,c_3649])).

tff(c_6135,plain,(
    ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6017,c_3809])).

tff(c_6156,plain,
    ( ~ v1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_6135])).

tff(c_6162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_94,c_3235,c_197,c_6156])).

tff(c_6163,plain,
    ( ~ v1_funct_1(k5_relat_1('#skF_5',k6_partfun1(k1_relat_1('#skF_4'))))
    | v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3618])).

tff(c_6186,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_5',k6_partfun1(k1_relat_1('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_6163])).

tff(c_6298,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_5',k6_partfun1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6292,c_6186])).

tff(c_9044,plain,(
    ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9040,c_6298])).

tff(c_9071,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_9044])).

tff(c_9077,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_94,c_3235,c_94,c_9071])).

tff(c_9078,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6163])).

tff(c_9095,plain,(
    ! [A_573,B_574,E_575] :
      ( v1_funct_1(k1_partfun1(A_573,B_574,'#skF_3','#skF_2',E_575,'#skF_5'))
      | ~ m1_subset_1(E_575,k1_zfmisc_1(k2_zfmisc_1(A_573,B_574)))
      | ~ v1_funct_1(E_575) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_3641])).

tff(c_9101,plain,
    ( v1_funct_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_9095])).

tff(c_9108,plain,(
    v1_funct_1(k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2286,c_9101])).

tff(c_9129,plain,(
    ! [A_578,C_579,B_580] :
      ( k6_partfun1(A_578) = k5_relat_1(C_579,k2_funct_1(C_579))
      | B_580 = '#skF_1'
      | ~ v2_funct_1(C_579)
      | k2_relset_1(A_578,B_580,C_579) != B_580
      | ~ m1_subset_1(C_579,k1_zfmisc_1(k2_zfmisc_1(A_578,B_580)))
      | ~ v1_funct_2(C_579,A_578,B_580)
      | ~ v1_funct_1(C_579) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_76])).

tff(c_9135,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_2','#skF_5') != '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_9129])).

tff(c_9145,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | '#skF_2' = '#skF_1'
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_1810,c_3235,c_9135])).

tff(c_9146,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_9145])).

tff(c_9189,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_9146])).

tff(c_9133,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_9129])).

tff(c_9141,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_88,c_84,c_9133])).

tff(c_9142,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_9141])).

tff(c_9150,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9142,c_393])).

tff(c_9154,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_100,c_84,c_558,c_10,c_326,c_107,c_9150])).

tff(c_9170,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9154,c_34])).

tff(c_9185,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_100,c_84,c_9170])).

tff(c_9190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9189,c_9185])).

tff(c_9192,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_9146])).

tff(c_9201,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_5')) = k2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9192,c_3244])).

tff(c_11054,plain,(
    ! [A_661,A_662] :
      ( k2_funct_1(k5_relat_1(A_661,k2_funct_1(A_662))) = k5_relat_1(A_662,k2_funct_1(A_661))
      | ~ v2_funct_1(k2_funct_1(A_662))
      | ~ v2_funct_1(A_661)
      | ~ v1_funct_1(k2_funct_1(A_662))
      | ~ v1_relat_1(k2_funct_1(A_662))
      | ~ v1_funct_1(A_661)
      | ~ v1_relat_1(A_661)
      | ~ v2_funct_1(A_662)
      | ~ v1_funct_1(A_662)
      | ~ v1_relat_1(A_662) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_605])).

tff(c_11111,plain,
    ( k5_relat_1('#skF_5',k2_funct_1(k6_partfun1('#skF_2'))) = k2_funct_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v1_funct_1(k6_partfun1('#skF_2'))
    | ~ v1_relat_1(k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9201,c_11054])).

tff(c_11145,plain,
    ( k5_relat_1('#skF_5',k6_partfun1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_94,c_3235,c_105,c_9108,c_3245,c_9078,c_104,c_102,c_11111])).

tff(c_11160,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_11145])).

tff(c_11163,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_11160])).

tff(c_11167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_94,c_3235,c_11163])).

tff(c_11168,plain,(
    k5_relat_1('#skF_5',k6_partfun1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_11145])).

tff(c_6164,plain,(
    v1_relat_1(k5_relat_1('#skF_5',k6_partfun1(k1_relat_1('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_3618])).

tff(c_9196,plain,(
    v1_relat_1(k5_relat_1('#skF_5',k6_partfun1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9192,c_6164])).

tff(c_9079,plain,(
    v1_funct_1(k5_relat_1('#skF_5',k6_partfun1(k1_relat_1('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_6163])).

tff(c_9195,plain,(
    v1_funct_1(k5_relat_1('#skF_5',k6_partfun1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9192,c_9079])).

tff(c_9197,plain,(
    k2_funct_1(k5_relat_1('#skF_5',k6_partfun1('#skF_2'))) = k2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9192,c_3575])).

tff(c_9389,plain,
    ( v2_funct_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1(k5_relat_1('#skF_5',k6_partfun1('#skF_2')))
    | ~ v1_funct_1(k5_relat_1('#skF_5',k6_partfun1('#skF_2')))
    | ~ v1_relat_1(k5_relat_1('#skF_5',k6_partfun1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9197,c_28])).

tff(c_9417,plain,
    ( v2_funct_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1(k5_relat_1('#skF_5',k6_partfun1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9196,c_9195,c_9389])).

tff(c_9437,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_5',k6_partfun1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_9417])).

tff(c_11170,plain,(
    ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11168,c_9437])).

tff(c_11204,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_11170])).

tff(c_11210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_94,c_3235,c_3235,c_11204])).

tff(c_11211,plain,(
    v2_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_9417])).

tff(c_9191,plain,(
    k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_9146])).

tff(c_11212,plain,(
    v2_funct_1(k5_relat_1('#skF_5',k6_partfun1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_9417])).

tff(c_9386,plain,
    ( k5_relat_1('#skF_5',k6_partfun1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1(k5_relat_1('#skF_5',k6_partfun1('#skF_2')))
    | ~ v1_funct_1(k5_relat_1('#skF_5',k6_partfun1('#skF_2')))
    | ~ v1_relat_1(k5_relat_1('#skF_5',k6_partfun1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9197,c_40])).

tff(c_9415,plain,
    ( k5_relat_1('#skF_5',k6_partfun1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1(k5_relat_1('#skF_5',k6_partfun1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9196,c_9195,c_9386])).

tff(c_11660,plain,(
    k5_relat_1('#skF_5',k6_partfun1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11212,c_9415])).

tff(c_14,plain,(
    ! [A_7] : k1_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_108,plain,(
    ! [A_7] : k1_relat_1(k6_partfun1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_14])).

tff(c_12,plain,(
    ! [B_6,A_4] :
      ( k2_relat_1(k5_relat_1(B_6,A_4)) = k2_relat_1(A_4)
      | ~ r1_tarski(k1_relat_1(A_4),k2_relat_1(B_6))
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1819,plain,(
    ! [A_4] :
      ( k2_relat_1(k5_relat_1('#skF_5',A_4)) = k2_relat_1(A_4)
      | ~ r1_tarski(k1_relat_1(A_4),k1_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1809,c_12])).

tff(c_3246,plain,(
    ! [A_299] :
      ( k2_relat_1(k5_relat_1('#skF_5',A_299)) = k2_relat_1(A_299)
      | ~ r1_tarski(k1_relat_1(A_299),k1_relat_1('#skF_4'))
      | ~ v1_relat_1(A_299) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_1819])).

tff(c_3252,plain,(
    ! [A_7] :
      ( k2_relat_1(k5_relat_1('#skF_5',k6_partfun1(A_7))) = k2_relat_1(k6_partfun1(A_7))
      | ~ r1_tarski(A_7,k1_relat_1('#skF_4'))
      | ~ v1_relat_1(k6_partfun1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_3246])).

tff(c_3258,plain,(
    ! [A_7] :
      ( k2_relat_1(k5_relat_1('#skF_5',k6_partfun1(A_7))) = A_7
      | ~ r1_tarski(A_7,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_107,c_3252])).

tff(c_9200,plain,(
    ! [A_7] :
      ( k2_relat_1(k5_relat_1('#skF_5',k6_partfun1(A_7))) = A_7
      | ~ r1_tarski(A_7,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9192,c_3258])).

tff(c_11668,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1('#skF_5'))) = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11660,c_9200])).

tff(c_11675,plain,(
    k2_relat_1(k2_funct_1(k2_funct_1('#skF_5'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_11668])).

tff(c_11714,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) = '#skF_2'
    | ~ v2_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11675,c_34])).

tff(c_11734,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3245,c_9078,c_11211,c_11714])).

tff(c_1827,plain,(
    ! [A_4] :
      ( k2_relat_1(k5_relat_1('#skF_5',A_4)) = k2_relat_1(A_4)
      | ~ r1_tarski(k1_relat_1(A_4),k1_relat_1('#skF_4'))
      | ~ v1_relat_1(A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_1819])).

tff(c_9202,plain,(
    ! [A_4] :
      ( k2_relat_1(k5_relat_1('#skF_5',A_4)) = k2_relat_1(A_4)
      | ~ r1_tarski(k1_relat_1(A_4),'#skF_2')
      | ~ v1_relat_1(A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9192,c_1827])).

tff(c_11743,plain,
    ( k2_relat_1(k5_relat_1('#skF_5',k2_funct_1('#skF_5'))) = k2_relat_1(k2_funct_1('#skF_5'))
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11734,c_9202])).

tff(c_11762,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3245,c_10,c_107,c_9191,c_11743])).

tff(c_11792,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_11762,c_34])).

tff(c_11809,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_94,c_3235,c_11792])).

tff(c_11843,plain,
    ( k5_relat_1(k6_partfun1('#skF_3'),'#skF_5') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_11809,c_106])).

tff(c_11853,plain,(
    k5_relat_1(k6_partfun1('#skF_3'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_11843])).

tff(c_11663,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11660,c_9196])).

tff(c_11664,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11660,c_9195])).

tff(c_11661,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11660,c_11212])).

tff(c_11662,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_5'))) = k2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11660,c_9197])).

tff(c_11894,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1('#skF_5'))) = k2_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11662,c_34])).

tff(c_11934,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_5'))) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11663,c_11664,c_11661,c_11762,c_11894])).

tff(c_11971,plain,
    ( k5_relat_1(k6_partfun1('#skF_3'),k2_funct_1(k2_funct_1('#skF_5'))) = k2_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11934,c_106])).

tff(c_11989,plain,(
    k5_relat_1(k6_partfun1('#skF_3'),k2_funct_1(k2_funct_1('#skF_5'))) = k2_funct_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11663,c_11971])).

tff(c_12133,plain,
    ( k5_relat_1(k6_partfun1('#skF_3'),'#skF_5') = k2_funct_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_11989])).

tff(c_12146,plain,(
    k2_funct_1(k2_funct_1('#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_94,c_3235,c_11853,c_12133])).

tff(c_14528,plain,(
    ! [A_762,B_763] :
      ( k2_funct_1(k2_funct_1(A_762)) = B_763
      | k5_relat_1(B_763,k2_funct_1(A_762)) != k6_partfun1(k1_relat_1(A_762))
      | k2_relat_1(B_763) != k1_relat_1(k2_funct_1(A_762))
      | ~ v2_funct_1(k2_funct_1(A_762))
      | ~ v1_funct_1(B_763)
      | ~ v1_relat_1(B_763)
      | ~ v1_funct_1(k2_funct_1(A_762))
      | ~ v1_relat_1(k2_funct_1(A_762))
      | ~ v2_funct_1(A_762)
      | ~ v1_funct_1(A_762)
      | ~ v1_relat_1(A_762) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_676])).

tff(c_14542,plain,(
    ! [B_763] :
      ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_5'))) = B_763
      | k6_partfun1(k1_relat_1(k2_funct_1('#skF_5'))) != k5_relat_1(B_763,'#skF_5')
      | k2_relat_1(B_763) != k1_relat_1(k2_funct_1(k2_funct_1('#skF_5')))
      | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_5')))
      | ~ v1_funct_1(B_763)
      | ~ v1_relat_1(B_763)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_5')))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_5')))
      | ~ v2_funct_1(k2_funct_1('#skF_5'))
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v1_relat_1(k2_funct_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12146,c_14528])).

tff(c_19169,plain,(
    ! [B_852] :
      ( k2_funct_1('#skF_5') = B_852
      | k5_relat_1(B_852,'#skF_5') != k6_partfun1('#skF_2')
      | k2_relat_1(B_852) != '#skF_3'
      | ~ v1_funct_1(B_852)
      | ~ v1_relat_1(B_852) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3245,c_9078,c_11211,c_197,c_12146,c_94,c_12146,c_3235,c_12146,c_11809,c_12146,c_11734,c_12146,c_14542])).

tff(c_19292,plain,
    ( k2_funct_1('#skF_5') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_5') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_3'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_196,c_19169])).

tff(c_19404,plain,(
    k2_funct_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_326,c_11452,c_19292])).

tff(c_19419,plain,(
    k2_funct_1('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19404,c_12146])).

tff(c_19430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_19419])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:13:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.15/6.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.15/6.07  
% 14.15/6.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.42/6.07  %$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 14.42/6.07  
% 14.42/6.07  %Foreground sorts:
% 14.42/6.07  
% 14.42/6.07  
% 14.42/6.07  %Background operators:
% 14.42/6.07  
% 14.42/6.07  
% 14.42/6.07  %Foreground operators:
% 14.42/6.07  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 14.42/6.07  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.42/6.07  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 14.42/6.07  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 14.42/6.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.42/6.07  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 14.42/6.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.42/6.07  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 14.42/6.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.42/6.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.42/6.07  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.42/6.07  tff('#skF_5', type, '#skF_5': $i).
% 14.42/6.07  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.42/6.07  tff('#skF_2', type, '#skF_2': $i).
% 14.42/6.07  tff('#skF_3', type, '#skF_3': $i).
% 14.42/6.07  tff('#skF_1', type, '#skF_1': $i).
% 14.42/6.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.42/6.07  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 14.42/6.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.42/6.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.42/6.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.42/6.07  tff('#skF_4', type, '#skF_4': $i).
% 14.42/6.07  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 14.42/6.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.42/6.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.42/6.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.42/6.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.42/6.07  
% 14.51/6.11  tff(f_257, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 14.51/6.11  tff(f_138, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 14.51/6.11  tff(f_170, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 14.51/6.11  tff(f_172, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 14.51/6.11  tff(f_148, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 14.51/6.11  tff(f_146, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 14.51/6.11  tff(f_160, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 14.51/6.11  tff(f_134, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 14.51/6.11  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 14.51/6.11  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 14.51/6.11  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 14.51/6.11  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.51/6.11  tff(f_50, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 14.51/6.11  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 14.51/6.11  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 14.51/6.11  tff(f_231, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 14.51/6.11  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 14.51/6.11  tff(f_105, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 14.51/6.11  tff(f_189, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 14.51/6.11  tff(f_66, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 14.51/6.11  tff(f_215, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 14.51/6.11  tff(f_113, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 14.51/6.11  tff(f_78, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 14.51/6.11  tff(f_130, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 14.51/6.11  tff(f_128, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(A) & v2_funct_1(B)) => (k2_funct_1(k5_relat_1(A, B)) = k5_relat_1(k2_funct_1(B), k2_funct_1(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_funct_1)).
% 14.51/6.11  tff(c_78, plain, (k2_funct_1('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_257])).
% 14.51/6.11  tff(c_100, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_257])).
% 14.51/6.11  tff(c_88, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_257])).
% 14.51/6.11  tff(c_96, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_257])).
% 14.51/6.11  tff(c_313, plain, (![A_87, B_88, C_89]: (k2_relset_1(A_87, B_88, C_89)=k2_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 14.51/6.11  tff(c_319, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_313])).
% 14.51/6.11  tff(c_326, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_319])).
% 14.51/6.11  tff(c_94, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_257])).
% 14.51/6.11  tff(c_90, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_257])).
% 14.51/6.11  tff(c_1943, plain, (![A_202, C_206, B_203, D_207, F_205, E_204]: (k1_partfun1(A_202, B_203, C_206, D_207, E_204, F_205)=k5_relat_1(E_204, F_205) | ~m1_subset_1(F_205, k1_zfmisc_1(k2_zfmisc_1(C_206, D_207))) | ~v1_funct_1(F_205) | ~m1_subset_1(E_204, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))) | ~v1_funct_1(E_204))), inference(cnfTransformation, [status(thm)], [f_170])).
% 14.51/6.11  tff(c_1949, plain, (![A_202, B_203, E_204]: (k1_partfun1(A_202, B_203, '#skF_3', '#skF_2', E_204, '#skF_5')=k5_relat_1(E_204, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_204, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))) | ~v1_funct_1(E_204))), inference(resolution, [status(thm)], [c_90, c_1943])).
% 14.51/6.11  tff(c_2070, plain, (![A_219, B_220, E_221]: (k1_partfun1(A_219, B_220, '#skF_3', '#skF_2', E_221, '#skF_5')=k5_relat_1(E_221, '#skF_5') | ~m1_subset_1(E_221, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))) | ~v1_funct_1(E_221))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1949])).
% 14.51/6.11  tff(c_2076, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_2070])).
% 14.51/6.11  tff(c_2083, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_2076])).
% 14.51/6.11  tff(c_62, plain, (![A_44]: (k6_relat_1(A_44)=k6_partfun1(A_44))), inference(cnfTransformation, [status(thm)], [f_172])).
% 14.51/6.11  tff(c_54, plain, (![A_31]: (m1_subset_1(k6_relat_1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 14.51/6.11  tff(c_101, plain, (![A_31]: (m1_subset_1(k6_partfun1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_54])).
% 14.51/6.11  tff(c_86, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_257])).
% 14.51/6.11  tff(c_581, plain, (![D_106, C_107, A_108, B_109]: (D_106=C_107 | ~r2_relset_1(A_108, B_109, C_107, D_106) | ~m1_subset_1(D_106, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 14.51/6.11  tff(c_589, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_86, c_581])).
% 14.51/6.11  tff(c_604, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_589])).
% 14.51/6.11  tff(c_1833, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_604])).
% 14.51/6.11  tff(c_2088, plain, (~m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2083, c_1833])).
% 14.51/6.11  tff(c_2228, plain, (![B_226, A_229, C_228, F_227, D_230, E_225]: (m1_subset_1(k1_partfun1(A_229, B_226, C_228, D_230, E_225, F_227), k1_zfmisc_1(k2_zfmisc_1(A_229, D_230))) | ~m1_subset_1(F_227, k1_zfmisc_1(k2_zfmisc_1(C_228, D_230))) | ~v1_funct_1(F_227) | ~m1_subset_1(E_225, k1_zfmisc_1(k2_zfmisc_1(A_229, B_226))) | ~v1_funct_1(E_225))), inference(cnfTransformation, [status(thm)], [f_160])).
% 14.51/6.11  tff(c_2262, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2083, c_2228])).
% 14.51/6.11  tff(c_2283, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_96, c_94, c_90, c_2262])).
% 14.51/6.11  tff(c_2285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2088, c_2283])).
% 14.51/6.11  tff(c_2286, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_604])).
% 14.51/6.11  tff(c_9080, plain, (![A_566, D_571, F_569, B_567, C_570, E_568]: (k1_partfun1(A_566, B_567, C_570, D_571, E_568, F_569)=k5_relat_1(E_568, F_569) | ~m1_subset_1(F_569, k1_zfmisc_1(k2_zfmisc_1(C_570, D_571))) | ~v1_funct_1(F_569) | ~m1_subset_1(E_568, k1_zfmisc_1(k2_zfmisc_1(A_566, B_567))) | ~v1_funct_1(E_568))), inference(cnfTransformation, [status(thm)], [f_170])).
% 14.51/6.11  tff(c_9086, plain, (![A_566, B_567, E_568]: (k1_partfun1(A_566, B_567, '#skF_3', '#skF_2', E_568, '#skF_5')=k5_relat_1(E_568, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_568, k1_zfmisc_1(k2_zfmisc_1(A_566, B_567))) | ~v1_funct_1(E_568))), inference(resolution, [status(thm)], [c_90, c_9080])).
% 14.51/6.11  tff(c_11429, plain, (![A_677, B_678, E_679]: (k1_partfun1(A_677, B_678, '#skF_3', '#skF_2', E_679, '#skF_5')=k5_relat_1(E_679, '#skF_5') | ~m1_subset_1(E_679, k1_zfmisc_1(k2_zfmisc_1(A_677, B_678))) | ~v1_funct_1(E_679))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_9086])).
% 14.51/6.11  tff(c_11441, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_11429])).
% 14.51/6.11  tff(c_11452, plain, (k5_relat_1('#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_2286, c_11441])).
% 14.51/6.11  tff(c_184, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 14.51/6.11  tff(c_196, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_184])).
% 14.51/6.11  tff(c_197, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_90, c_184])).
% 14.51/6.11  tff(c_22, plain, (![A_9]: (v1_relat_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_62])).
% 14.51/6.11  tff(c_84, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_257])).
% 14.51/6.11  tff(c_275, plain, (![A_84]: (k1_relat_1(k2_funct_1(A_84))=k2_relat_1(A_84) | ~v2_funct_1(A_84) | ~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.51/6.11  tff(c_18, plain, (![A_8]: (k5_relat_1(k6_relat_1(k1_relat_1(A_8)), A_8)=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.51/6.11  tff(c_106, plain, (![A_8]: (k5_relat_1(k6_partfun1(k1_relat_1(A_8)), A_8)=A_8 | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_18])).
% 14.51/6.11  tff(c_479, plain, (![A_100]: (k5_relat_1(k6_partfun1(k2_relat_1(A_100)), k2_funct_1(A_100))=k2_funct_1(A_100) | ~v1_relat_1(k2_funct_1(A_100)) | ~v2_funct_1(A_100) | ~v1_funct_1(A_100) | ~v1_relat_1(A_100))), inference(superposition, [status(thm), theory('equality')], [c_275, c_106])).
% 14.51/6.11  tff(c_503, plain, (k5_relat_1(k6_partfun1('#skF_3'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_326, c_479])).
% 14.51/6.11  tff(c_520, plain, (k5_relat_1(k6_partfun1('#skF_3'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_100, c_84, c_503])).
% 14.51/6.11  tff(c_525, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_520])).
% 14.51/6.11  tff(c_552, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_525])).
% 14.51/6.11  tff(c_556, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_196, c_100, c_552])).
% 14.51/6.11  tff(c_558, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_520])).
% 14.51/6.11  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.51/6.11  tff(c_16, plain, (![A_7]: (k2_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_50])).
% 14.51/6.11  tff(c_107, plain, (![A_7]: (k2_relat_1(k6_partfun1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_16])).
% 14.51/6.11  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.51/6.11  tff(c_113, plain, (![A_63]: (k1_xboole_0=A_63 | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.51/6.11  tff(c_117, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_113])).
% 14.51/6.11  tff(c_80, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_257])).
% 14.51/6.11  tff(c_119, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_80])).
% 14.51/6.11  tff(c_98, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_257])).
% 14.51/6.11  tff(c_76, plain, (![A_56, C_58, B_57]: (k6_partfun1(A_56)=k5_relat_1(C_58, k2_funct_1(C_58)) | k1_xboole_0=B_57 | ~v2_funct_1(C_58) | k2_relset_1(A_56, B_57, C_58)!=B_57 | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_2(C_58, A_56, B_57) | ~v1_funct_1(C_58))), inference(cnfTransformation, [status(thm)], [f_231])).
% 14.51/6.11  tff(c_929, plain, (![A_148, C_149, B_150]: (k6_partfun1(A_148)=k5_relat_1(C_149, k2_funct_1(C_149)) | B_150='#skF_1' | ~v2_funct_1(C_149) | k2_relset_1(A_148, B_150, C_149)!=B_150 | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_148, B_150))) | ~v1_funct_2(C_149, A_148, B_150) | ~v1_funct_1(C_149))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_76])).
% 14.51/6.11  tff(c_933, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_929])).
% 14.51/6.11  tff(c_941, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_88, c_84, c_933])).
% 14.51/6.11  tff(c_942, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_119, c_941])).
% 14.51/6.11  tff(c_36, plain, (![A_12]: (k1_relat_1(k2_funct_1(A_12))=k2_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.51/6.11  tff(c_341, plain, (![B_91, A_92]: (k2_relat_1(k5_relat_1(B_91, A_92))=k2_relat_1(A_92) | ~r1_tarski(k1_relat_1(A_92), k2_relat_1(B_91)) | ~v1_relat_1(B_91) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.51/6.11  tff(c_344, plain, (![A_92]: (k2_relat_1(k5_relat_1('#skF_4', A_92))=k2_relat_1(A_92) | ~r1_tarski(k1_relat_1(A_92), '#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_92))), inference(superposition, [status(thm), theory('equality')], [c_326, c_341])).
% 14.51/6.11  tff(c_390, plain, (![A_95]: (k2_relat_1(k5_relat_1('#skF_4', A_95))=k2_relat_1(A_95) | ~r1_tarski(k1_relat_1(A_95), '#skF_3') | ~v1_relat_1(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_344])).
% 14.51/6.11  tff(c_393, plain, (![A_12]: (k2_relat_1(k5_relat_1('#skF_4', k2_funct_1(A_12)))=k2_relat_1(k2_funct_1(A_12)) | ~r1_tarski(k2_relat_1(A_12), '#skF_3') | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_36, c_390])).
% 14.51/6.11  tff(c_950, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1(k2_funct_1('#skF_4')) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_942, c_393])).
% 14.51/6.11  tff(c_954, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_100, c_84, c_558, c_10, c_326, c_107, c_950])).
% 14.51/6.11  tff(c_34, plain, (![A_12]: (k2_relat_1(k2_funct_1(A_12))=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.51/6.11  tff(c_970, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_954, c_34])).
% 14.51/6.11  tff(c_985, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_100, c_84, c_970])).
% 14.51/6.11  tff(c_38, plain, (![A_13, B_15]: (k2_funct_1(A_13)=B_15 | k6_relat_1(k2_relat_1(A_13))!=k5_relat_1(B_15, A_13) | k2_relat_1(B_15)!=k1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_105])).
% 14.51/6.11  tff(c_676, plain, (![A_114, B_115]: (k2_funct_1(A_114)=B_115 | k6_partfun1(k2_relat_1(A_114))!=k5_relat_1(B_115, A_114) | k2_relat_1(B_115)!=k1_relat_1(A_114) | ~v2_funct_1(A_114) | ~v1_funct_1(B_115) | ~v1_relat_1(B_115) | ~v1_funct_1(A_114) | ~v1_relat_1(A_114))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_38])).
% 14.51/6.11  tff(c_694, plain, (![B_115]: (k2_funct_1('#skF_4')=B_115 | k5_relat_1(B_115, '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1(B_115)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_115) | ~v1_relat_1(B_115) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_326, c_676])).
% 14.51/6.11  tff(c_717, plain, (![B_116]: (k2_funct_1('#skF_4')=B_116 | k5_relat_1(B_116, '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1(B_116)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_116) | ~v1_relat_1(B_116))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_100, c_84, c_694])).
% 14.51/6.11  tff(c_723, plain, (k2_funct_1('#skF_4')='#skF_5' | k5_relat_1('#skF_5', '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_197, c_717])).
% 14.51/6.11  tff(c_737, plain, (k2_funct_1('#skF_4')='#skF_5' | k5_relat_1('#skF_5', '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1('#skF_5')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_723])).
% 14.51/6.11  tff(c_738, plain, (k5_relat_1('#skF_5', '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1('#skF_5')!=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_78, c_737])).
% 14.51/6.11  tff(c_745, plain, (k2_relat_1('#skF_5')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_738])).
% 14.51/6.11  tff(c_991, plain, (k2_relat_1('#skF_5')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_985, c_745])).
% 14.51/6.11  tff(c_92, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_257])).
% 14.51/6.11  tff(c_265, plain, (![A_81, B_82, D_83]: (r2_relset_1(A_81, B_82, D_83, D_83) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 14.51/6.11  tff(c_272, plain, (![A_31]: (r2_relset_1(A_31, A_31, k6_partfun1(A_31), k6_partfun1(A_31)))), inference(resolution, [status(thm)], [c_101, c_265])).
% 14.51/6.11  tff(c_327, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_90, c_313])).
% 14.51/6.11  tff(c_863, plain, (![F_138, B_136, E_137, C_139, D_140, A_135]: (k1_partfun1(A_135, B_136, C_139, D_140, E_137, F_138)=k5_relat_1(E_137, F_138) | ~m1_subset_1(F_138, k1_zfmisc_1(k2_zfmisc_1(C_139, D_140))) | ~v1_funct_1(F_138) | ~m1_subset_1(E_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))) | ~v1_funct_1(E_137))), inference(cnfTransformation, [status(thm)], [f_170])).
% 14.51/6.11  tff(c_869, plain, (![A_135, B_136, E_137]: (k1_partfun1(A_135, B_136, '#skF_3', '#skF_2', E_137, '#skF_5')=k5_relat_1(E_137, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))) | ~v1_funct_1(E_137))), inference(resolution, [status(thm)], [c_90, c_863])).
% 14.51/6.11  tff(c_905, plain, (![A_145, B_146, E_147]: (k1_partfun1(A_145, B_146, '#skF_3', '#skF_2', E_147, '#skF_5')=k5_relat_1(E_147, '#skF_5') | ~m1_subset_1(E_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~v1_funct_1(E_147))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_869])).
% 14.51/6.11  tff(c_911, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_905])).
% 14.51/6.11  tff(c_918, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_911])).
% 14.51/6.11  tff(c_1304, plain, (![F_163, D_166, A_165, C_164, B_162, E_161]: (m1_subset_1(k1_partfun1(A_165, B_162, C_164, D_166, E_161, F_163), k1_zfmisc_1(k2_zfmisc_1(A_165, D_166))) | ~m1_subset_1(F_163, k1_zfmisc_1(k2_zfmisc_1(C_164, D_166))) | ~v1_funct_1(F_163) | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(A_165, B_162))) | ~v1_funct_1(E_161))), inference(cnfTransformation, [status(thm)], [f_160])).
% 14.51/6.11  tff(c_1341, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_918, c_1304])).
% 14.51/6.11  tff(c_1364, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_96, c_94, c_90, c_1341])).
% 14.51/6.11  tff(c_1484, plain, (k5_relat_1('#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1364, c_918, c_918, c_604])).
% 14.51/6.11  tff(c_1488, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1484, c_918])).
% 14.51/6.11  tff(c_1797, plain, (![A_183, B_184, C_185, D_186]: (k2_relset_1(A_183, B_184, C_185)=B_184 | ~r2_relset_1(B_184, B_184, k1_partfun1(B_184, A_183, A_183, B_184, D_186, C_185), k6_partfun1(B_184)) | ~m1_subset_1(D_186, k1_zfmisc_1(k2_zfmisc_1(B_184, A_183))) | ~v1_funct_2(D_186, B_184, A_183) | ~v1_funct_1(D_186) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~v1_funct_2(C_185, A_183, B_184) | ~v1_funct_1(C_185))), inference(cnfTransformation, [status(thm)], [f_189])).
% 14.51/6.11  tff(c_1800, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1488, c_1797])).
% 14.51/6.11  tff(c_1805, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_90, c_100, c_98, c_96, c_272, c_327, c_1800])).
% 14.51/6.11  tff(c_1807, plain, $false, inference(negUnitSimplification, [status(thm)], [c_991, c_1805])).
% 14.51/6.11  tff(c_1809, plain, (k2_relat_1('#skF_5')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_738])).
% 14.51/6.11  tff(c_281, plain, (![A_84]: (k5_relat_1(k6_partfun1(k2_relat_1(A_84)), k2_funct_1(A_84))=k2_funct_1(A_84) | ~v1_relat_1(k2_funct_1(A_84)) | ~v2_funct_1(A_84) | ~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(superposition, [status(thm), theory('equality')], [c_275, c_106])).
% 14.51/6.11  tff(c_1816, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k2_funct_1('#skF_5'))=k2_funct_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1809, c_281])).
% 14.51/6.11  tff(c_1825, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k2_funct_1('#skF_5'))=k2_funct_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_94, c_1816])).
% 14.51/6.11  tff(c_2296, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_1825])).
% 14.51/6.11  tff(c_82, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_257])).
% 14.51/6.11  tff(c_120, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_82])).
% 14.51/6.11  tff(c_26, plain, (![A_10]: (v2_funct_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 14.51/6.11  tff(c_104, plain, (![A_10]: (v2_funct_1(k6_partfun1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_26])).
% 14.51/6.11  tff(c_68, plain, (![A_50, E_55, B_51, C_52, D_53]: (k1_xboole_0=C_52 | v2_funct_1(E_55) | k2_relset_1(A_50, B_51, D_53)!=B_51 | ~v2_funct_1(k1_partfun1(A_50, B_51, B_51, C_52, D_53, E_55)) | ~m1_subset_1(E_55, k1_zfmisc_1(k2_zfmisc_1(B_51, C_52))) | ~v1_funct_2(E_55, B_51, C_52) | ~v1_funct_1(E_55) | ~m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | ~v1_funct_2(D_53, A_50, B_51) | ~v1_funct_1(D_53))), inference(cnfTransformation, [status(thm)], [f_215])).
% 14.51/6.11  tff(c_3222, plain, (![C_296, A_294, B_297, D_298, E_295]: (C_296='#skF_1' | v2_funct_1(E_295) | k2_relset_1(A_294, B_297, D_298)!=B_297 | ~v2_funct_1(k1_partfun1(A_294, B_297, B_297, C_296, D_298, E_295)) | ~m1_subset_1(E_295, k1_zfmisc_1(k2_zfmisc_1(B_297, C_296))) | ~v1_funct_2(E_295, B_297, C_296) | ~v1_funct_1(E_295) | ~m1_subset_1(D_298, k1_zfmisc_1(k2_zfmisc_1(A_294, B_297))) | ~v1_funct_2(D_298, A_294, B_297) | ~v1_funct_1(D_298))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_68])).
% 14.51/6.11  tff(c_3226, plain, ('#skF_2'='#skF_1' | v2_funct_1('#skF_5') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2286, c_3222])).
% 14.51/6.11  tff(c_3231, plain, ('#skF_2'='#skF_1' | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_96, c_94, c_92, c_90, c_104, c_88, c_3226])).
% 14.51/6.11  tff(c_3233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2296, c_120, c_3231])).
% 14.51/6.11  tff(c_3234, plain, (~v1_relat_1(k2_funct_1('#skF_5')) | k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k2_funct_1('#skF_5'))=k2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_1825])).
% 14.51/6.11  tff(c_3236, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_3234])).
% 14.51/6.11  tff(c_3239, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_3236])).
% 14.51/6.11  tff(c_3243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_94, c_3239])).
% 14.51/6.11  tff(c_3245, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_3234])).
% 14.51/6.11  tff(c_3235, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_1825])).
% 14.51/6.11  tff(c_40, plain, (![A_16]: (k2_funct_1(k2_funct_1(A_16))=A_16 | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.51/6.11  tff(c_28, plain, (![A_11]: (v2_funct_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_78])).
% 14.51/6.11  tff(c_20, plain, (![A_9]: (v1_funct_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_62])).
% 14.51/6.11  tff(c_24, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 14.51/6.11  tff(c_105, plain, (![A_10]: (v1_relat_1(k6_partfun1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_24])).
% 14.51/6.11  tff(c_3635, plain, (![A_341, B_338, F_339, C_340, E_337, D_342]: (v1_funct_1(k1_partfun1(A_341, B_338, C_340, D_342, E_337, F_339)) | ~m1_subset_1(F_339, k1_zfmisc_1(k2_zfmisc_1(C_340, D_342))) | ~v1_funct_1(F_339) | ~m1_subset_1(E_337, k1_zfmisc_1(k2_zfmisc_1(A_341, B_338))) | ~v1_funct_1(E_337))), inference(cnfTransformation, [status(thm)], [f_160])).
% 14.51/6.11  tff(c_3641, plain, (![A_341, B_338, E_337]: (v1_funct_1(k1_partfun1(A_341, B_338, '#skF_3', '#skF_2', E_337, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_337, k1_zfmisc_1(k2_zfmisc_1(A_341, B_338))) | ~v1_funct_1(E_337))), inference(resolution, [status(thm)], [c_90, c_3635])).
% 14.51/6.11  tff(c_6202, plain, (![A_463, B_464, E_465]: (v1_funct_1(k1_partfun1(A_463, B_464, '#skF_3', '#skF_2', E_465, '#skF_5')) | ~m1_subset_1(E_465, k1_zfmisc_1(k2_zfmisc_1(A_463, B_464))) | ~v1_funct_1(E_465))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_3641])).
% 14.51/6.11  tff(c_6208, plain, (v1_funct_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_6202])).
% 14.51/6.11  tff(c_6215, plain, (v1_funct_1(k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_2286, c_6208])).
% 14.51/6.11  tff(c_44, plain, (![A_20]: (k2_funct_1(k6_relat_1(A_20))=k6_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_130])).
% 14.51/6.11  tff(c_102, plain, (![A_20]: (k2_funct_1(k6_partfun1(A_20))=k6_partfun1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_44])).
% 14.51/6.11  tff(c_6236, plain, (![A_468, C_469, B_470]: (k6_partfun1(A_468)=k5_relat_1(C_469, k2_funct_1(C_469)) | B_470='#skF_1' | ~v2_funct_1(C_469) | k2_relset_1(A_468, B_470, C_469)!=B_470 | ~m1_subset_1(C_469, k1_zfmisc_1(k2_zfmisc_1(A_468, B_470))) | ~v1_funct_2(C_469, A_468, B_470) | ~v1_funct_1(C_469))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_76])).
% 14.51/6.11  tff(c_6240, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_6236])).
% 14.51/6.11  tff(c_6248, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_88, c_84, c_6240])).
% 14.51/6.11  tff(c_6249, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_119, c_6248])).
% 14.51/6.11  tff(c_6257, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1(k2_funct_1('#skF_4')) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6249, c_393])).
% 14.51/6.11  tff(c_6261, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_100, c_84, c_558, c_10, c_326, c_107, c_6257])).
% 14.51/6.11  tff(c_6277, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6261, c_34])).
% 14.51/6.11  tff(c_6292, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_100, c_84, c_6277])).
% 14.51/6.11  tff(c_3244, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k2_funct_1('#skF_5'))=k2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_3234])).
% 14.51/6.11  tff(c_6304, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_5'))=k2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6292, c_3244])).
% 14.51/6.11  tff(c_605, plain, (![B_110, A_111]: (k5_relat_1(k2_funct_1(B_110), k2_funct_1(A_111))=k2_funct_1(k5_relat_1(A_111, B_110)) | ~v2_funct_1(B_110) | ~v2_funct_1(A_111) | ~v1_funct_1(B_110) | ~v1_relat_1(B_110) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.51/6.11  tff(c_8534, plain, (![A_551, A_552]: (k2_funct_1(k5_relat_1(A_551, k2_funct_1(A_552)))=k5_relat_1(A_552, k2_funct_1(A_551)) | ~v2_funct_1(k2_funct_1(A_552)) | ~v2_funct_1(A_551) | ~v1_funct_1(k2_funct_1(A_552)) | ~v1_relat_1(k2_funct_1(A_552)) | ~v1_funct_1(A_551) | ~v1_relat_1(A_551) | ~v2_funct_1(A_552) | ~v1_funct_1(A_552) | ~v1_relat_1(A_552))), inference(superposition, [status(thm), theory('equality')], [c_40, c_605])).
% 14.51/6.11  tff(c_8591, plain, (k5_relat_1('#skF_5', k2_funct_1(k6_partfun1('#skF_2')))=k2_funct_1(k2_funct_1('#skF_5')) | ~v2_funct_1(k2_funct_1('#skF_5')) | ~v2_funct_1(k6_partfun1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v1_funct_1(k6_partfun1('#skF_2')) | ~v1_relat_1(k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6304, c_8534])).
% 14.51/6.11  tff(c_8625, plain, (k5_relat_1('#skF_5', k6_partfun1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_5')) | ~v2_funct_1(k2_funct_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_94, c_3235, c_105, c_6215, c_3245, c_104, c_102, c_8591])).
% 14.51/6.11  tff(c_8917, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_8625])).
% 14.51/6.11  tff(c_8920, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_8917])).
% 14.51/6.11  tff(c_8924, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_94, c_8920])).
% 14.51/6.11  tff(c_8925, plain, (~v2_funct_1(k2_funct_1('#skF_5')) | k5_relat_1('#skF_5', k6_partfun1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_8625])).
% 14.51/6.11  tff(c_9032, plain, (~v2_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_8925])).
% 14.51/6.11  tff(c_9035, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_9032])).
% 14.51/6.11  tff(c_9039, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_94, c_3235, c_9035])).
% 14.51/6.11  tff(c_9040, plain, (k5_relat_1('#skF_5', k6_partfun1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_8925])).
% 14.51/6.11  tff(c_3668, plain, (![A_347, B_348, E_349]: (v1_funct_1(k1_partfun1(A_347, B_348, '#skF_3', '#skF_2', E_349, '#skF_5')) | ~m1_subset_1(E_349, k1_zfmisc_1(k2_zfmisc_1(A_347, B_348))) | ~v1_funct_1(E_349))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_3641])).
% 14.51/6.11  tff(c_3674, plain, (v1_funct_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_3668])).
% 14.51/6.11  tff(c_3681, plain, (v1_funct_1(k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_2286, c_3674])).
% 14.51/6.11  tff(c_1810, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1809, c_327])).
% 14.51/6.11  tff(c_3743, plain, (![A_361, C_362, B_363]: (k6_partfun1(A_361)=k5_relat_1(C_362, k2_funct_1(C_362)) | B_363='#skF_1' | ~v2_funct_1(C_362) | k2_relset_1(A_361, B_363, C_362)!=B_363 | ~m1_subset_1(C_362, k1_zfmisc_1(k2_zfmisc_1(A_361, B_363))) | ~v1_funct_2(C_362, A_361, B_363) | ~v1_funct_1(C_362))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_76])).
% 14.51/6.11  tff(c_3749, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_2', '#skF_5')!='#skF_2' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_90, c_3743])).
% 14.51/6.11  tff(c_3759, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | '#skF_2'='#skF_1' | k1_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_1810, c_3235, c_3749])).
% 14.51/6.11  tff(c_3760, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | k1_relat_1('#skF_4')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_120, c_3759])).
% 14.51/6.11  tff(c_3803, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_3760])).
% 14.51/6.11  tff(c_3747, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_3743])).
% 14.51/6.11  tff(c_3755, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_88, c_84, c_3747])).
% 14.51/6.11  tff(c_3756, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_119, c_3755])).
% 14.51/6.11  tff(c_3764, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1(k2_funct_1('#skF_4')) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3756, c_393])).
% 14.51/6.11  tff(c_3768, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_100, c_84, c_558, c_10, c_326, c_107, c_3764])).
% 14.51/6.11  tff(c_3784, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3768, c_34])).
% 14.51/6.11  tff(c_3799, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_100, c_84, c_3784])).
% 14.51/6.11  tff(c_3804, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3803, c_3799])).
% 14.51/6.11  tff(c_3806, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_3760])).
% 14.51/6.11  tff(c_3814, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_5'))=k2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3806, c_3244])).
% 14.51/6.11  tff(c_5706, plain, (![A_439, A_440]: (k2_funct_1(k5_relat_1(A_439, k2_funct_1(A_440)))=k5_relat_1(A_440, k2_funct_1(A_439)) | ~v2_funct_1(k2_funct_1(A_440)) | ~v2_funct_1(A_439) | ~v1_funct_1(k2_funct_1(A_440)) | ~v1_relat_1(k2_funct_1(A_440)) | ~v1_funct_1(A_439) | ~v1_relat_1(A_439) | ~v2_funct_1(A_440) | ~v1_funct_1(A_440) | ~v1_relat_1(A_440))), inference(superposition, [status(thm), theory('equality')], [c_40, c_605])).
% 14.51/6.11  tff(c_5763, plain, (k5_relat_1('#skF_5', k2_funct_1(k6_partfun1('#skF_2')))=k2_funct_1(k2_funct_1('#skF_5')) | ~v2_funct_1(k2_funct_1('#skF_5')) | ~v2_funct_1(k6_partfun1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v1_funct_1(k6_partfun1('#skF_2')) | ~v1_relat_1(k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3814, c_5706])).
% 14.51/6.11  tff(c_5797, plain, (k5_relat_1('#skF_5', k6_partfun1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_5')) | ~v2_funct_1(k2_funct_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_94, c_3235, c_105, c_3681, c_3245, c_104, c_102, c_5763])).
% 14.51/6.11  tff(c_5999, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_5797])).
% 14.51/6.11  tff(c_6002, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_5999])).
% 14.51/6.11  tff(c_6006, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_94, c_6002])).
% 14.51/6.11  tff(c_6007, plain, (~v2_funct_1(k2_funct_1('#skF_5')) | k5_relat_1('#skF_5', k6_partfun1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_5797])).
% 14.51/6.11  tff(c_6009, plain, (~v2_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_6007])).
% 14.51/6.11  tff(c_6012, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_6009])).
% 14.51/6.11  tff(c_6016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_94, c_3235, c_6012])).
% 14.51/6.11  tff(c_6017, plain, (k5_relat_1('#skF_5', k6_partfun1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_6007])).
% 14.51/6.11  tff(c_3333, plain, (![E_301, B_302, D_306, C_304, F_303, A_305]: (v1_funct_1(k1_partfun1(A_305, B_302, C_304, D_306, E_301, F_303)) | ~m1_subset_1(F_303, k1_zfmisc_1(k2_zfmisc_1(C_304, D_306))) | ~v1_funct_1(F_303) | ~m1_subset_1(E_301, k1_zfmisc_1(k2_zfmisc_1(A_305, B_302))) | ~v1_funct_1(E_301))), inference(cnfTransformation, [status(thm)], [f_160])).
% 14.51/6.11  tff(c_3339, plain, (![A_305, B_302, E_301]: (v1_funct_1(k1_partfun1(A_305, B_302, '#skF_3', '#skF_2', E_301, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_301, k1_zfmisc_1(k2_zfmisc_1(A_305, B_302))) | ~v1_funct_1(E_301))), inference(resolution, [status(thm)], [c_90, c_3333])).
% 14.51/6.11  tff(c_3365, plain, (![A_311, B_312, E_313]: (v1_funct_1(k1_partfun1(A_311, B_312, '#skF_3', '#skF_2', E_313, '#skF_5')) | ~m1_subset_1(E_313, k1_zfmisc_1(k2_zfmisc_1(A_311, B_312))) | ~v1_funct_1(E_313))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_3339])).
% 14.51/6.11  tff(c_3371, plain, (v1_funct_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_3365])).
% 14.51/6.11  tff(c_3378, plain, (v1_funct_1(k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_2286, c_3371])).
% 14.51/6.11  tff(c_732, plain, (![A_10]: (k6_partfun1(A_10)=k2_funct_1('#skF_4') | k5_relat_1(k6_partfun1(A_10), '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1(k6_partfun1(A_10))!=k1_relat_1('#skF_4') | ~v1_funct_1(k6_partfun1(A_10)))), inference(resolution, [status(thm)], [c_105, c_717])).
% 14.51/6.11  tff(c_3397, plain, (![A_321]: (k6_partfun1(A_321)=k2_funct_1('#skF_4') | k5_relat_1(k6_partfun1(A_321), '#skF_4')!=k6_partfun1('#skF_3') | k1_relat_1('#skF_4')!=A_321 | ~v1_funct_1(k6_partfun1(A_321)))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_732])).
% 14.51/6.11  tff(c_3401, plain, (k6_partfun1('#skF_2')=k2_funct_1('#skF_4') | k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')!=k6_partfun1('#skF_3') | k1_relat_1('#skF_4')!='#skF_2'), inference(resolution, [status(thm)], [c_3378, c_3397])).
% 14.51/6.11  tff(c_3402, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_3401])).
% 14.51/6.11  tff(c_3502, plain, (![A_333, C_334, B_335]: (k6_partfun1(A_333)=k5_relat_1(C_334, k2_funct_1(C_334)) | B_335='#skF_1' | ~v2_funct_1(C_334) | k2_relset_1(A_333, B_335, C_334)!=B_335 | ~m1_subset_1(C_334, k1_zfmisc_1(k2_zfmisc_1(A_333, B_335))) | ~v1_funct_2(C_334, A_333, B_335) | ~v1_funct_1(C_334))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_76])).
% 14.51/6.11  tff(c_3506, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_3502])).
% 14.51/6.11  tff(c_3514, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_88, c_84, c_3506])).
% 14.51/6.11  tff(c_3515, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_119, c_3514])).
% 14.51/6.11  tff(c_3523, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1(k2_funct_1('#skF_4')) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3515, c_393])).
% 14.51/6.11  tff(c_3527, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_100, c_84, c_558, c_10, c_326, c_107, c_3523])).
% 14.51/6.11  tff(c_3543, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3527, c_34])).
% 14.51/6.11  tff(c_3558, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_100, c_84, c_3543])).
% 14.51/6.11  tff(c_3560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3402, c_3558])).
% 14.51/6.11  tff(c_3562, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_3401])).
% 14.51/6.11  tff(c_620, plain, (![A_20, A_111]: (k5_relat_1(k6_partfun1(A_20), k2_funct_1(A_111))=k2_funct_1(k5_relat_1(A_111, k6_partfun1(A_20))) | ~v2_funct_1(k6_partfun1(A_20)) | ~v2_funct_1(A_111) | ~v1_funct_1(k6_partfun1(A_20)) | ~v1_relat_1(k6_partfun1(A_20)) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(superposition, [status(thm), theory('equality')], [c_102, c_605])).
% 14.51/6.11  tff(c_627, plain, (![A_20, A_111]: (k5_relat_1(k6_partfun1(A_20), k2_funct_1(A_111))=k2_funct_1(k5_relat_1(A_111, k6_partfun1(A_20))) | ~v2_funct_1(A_111) | ~v1_funct_1(k6_partfun1(A_20)) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_104, c_620])).
% 14.51/6.11  tff(c_3283, plain, (k2_funct_1(k5_relat_1('#skF_5', k6_partfun1(k1_relat_1('#skF_4'))))=k2_funct_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1(k6_partfun1(k1_relat_1('#skF_4'))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3244, c_627])).
% 14.51/6.11  tff(c_3295, plain, (k2_funct_1(k5_relat_1('#skF_5', k6_partfun1(k1_relat_1('#skF_4'))))=k2_funct_1('#skF_5') | ~v1_funct_1(k6_partfun1(k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_94, c_3235, c_3283])).
% 14.51/6.11  tff(c_3332, plain, (~v1_funct_1(k6_partfun1(k1_relat_1('#skF_4')))), inference(splitLeft, [status(thm)], [c_3295])).
% 14.51/6.11  tff(c_3564, plain, (~v1_funct_1(k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3562, c_3332])).
% 14.51/6.11  tff(c_3574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3378, c_3564])).
% 14.51/6.11  tff(c_3575, plain, (k2_funct_1(k5_relat_1('#skF_5', k6_partfun1(k1_relat_1('#skF_4'))))=k2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_3295])).
% 14.51/6.11  tff(c_3618, plain, (v1_funct_1(k2_funct_1('#skF_5')) | ~v1_funct_1(k5_relat_1('#skF_5', k6_partfun1(k1_relat_1('#skF_4')))) | ~v1_relat_1(k5_relat_1('#skF_5', k6_partfun1(k1_relat_1('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_3575, c_20])).
% 14.51/6.11  tff(c_3649, plain, (~v1_relat_1(k5_relat_1('#skF_5', k6_partfun1(k1_relat_1('#skF_4'))))), inference(splitLeft, [status(thm)], [c_3618])).
% 14.51/6.11  tff(c_3809, plain, (~v1_relat_1(k5_relat_1('#skF_5', k6_partfun1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3806, c_3649])).
% 14.51/6.11  tff(c_6135, plain, (~v1_relat_1(k2_funct_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_6017, c_3809])).
% 14.51/6.11  tff(c_6156, plain, (~v1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_40, c_6135])).
% 14.51/6.11  tff(c_6162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_94, c_3235, c_197, c_6156])).
% 14.51/6.11  tff(c_6163, plain, (~v1_funct_1(k5_relat_1('#skF_5', k6_partfun1(k1_relat_1('#skF_4')))) | v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_3618])).
% 14.51/6.11  tff(c_6186, plain, (~v1_funct_1(k5_relat_1('#skF_5', k6_partfun1(k1_relat_1('#skF_4'))))), inference(splitLeft, [status(thm)], [c_6163])).
% 14.51/6.11  tff(c_6298, plain, (~v1_funct_1(k5_relat_1('#skF_5', k6_partfun1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6292, c_6186])).
% 14.51/6.11  tff(c_9044, plain, (~v1_funct_1(k2_funct_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_9040, c_6298])).
% 14.51/6.11  tff(c_9071, plain, (~v1_funct_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_40, c_9044])).
% 14.51/6.11  tff(c_9077, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_94, c_3235, c_94, c_9071])).
% 14.51/6.11  tff(c_9078, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_6163])).
% 14.51/6.11  tff(c_9095, plain, (![A_573, B_574, E_575]: (v1_funct_1(k1_partfun1(A_573, B_574, '#skF_3', '#skF_2', E_575, '#skF_5')) | ~m1_subset_1(E_575, k1_zfmisc_1(k2_zfmisc_1(A_573, B_574))) | ~v1_funct_1(E_575))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_3641])).
% 14.51/6.11  tff(c_9101, plain, (v1_funct_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_9095])).
% 14.51/6.11  tff(c_9108, plain, (v1_funct_1(k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_2286, c_9101])).
% 14.51/6.11  tff(c_9129, plain, (![A_578, C_579, B_580]: (k6_partfun1(A_578)=k5_relat_1(C_579, k2_funct_1(C_579)) | B_580='#skF_1' | ~v2_funct_1(C_579) | k2_relset_1(A_578, B_580, C_579)!=B_580 | ~m1_subset_1(C_579, k1_zfmisc_1(k2_zfmisc_1(A_578, B_580))) | ~v1_funct_2(C_579, A_578, B_580) | ~v1_funct_1(C_579))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_76])).
% 14.51/6.11  tff(c_9135, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_2', '#skF_5')!='#skF_2' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_90, c_9129])).
% 14.51/6.11  tff(c_9145, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | '#skF_2'='#skF_1' | k1_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_1810, c_3235, c_9135])).
% 14.51/6.11  tff(c_9146, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | k1_relat_1('#skF_4')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_120, c_9145])).
% 14.51/6.11  tff(c_9189, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_9146])).
% 14.51/6.11  tff(c_9133, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_9129])).
% 14.51/6.11  tff(c_9141, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_88, c_84, c_9133])).
% 14.51/6.11  tff(c_9142, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_119, c_9141])).
% 14.51/6.11  tff(c_9150, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1(k2_funct_1('#skF_4')) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9142, c_393])).
% 14.51/6.11  tff(c_9154, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_100, c_84, c_558, c_10, c_326, c_107, c_9150])).
% 14.51/6.11  tff(c_9170, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9154, c_34])).
% 14.51/6.11  tff(c_9185, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_100, c_84, c_9170])).
% 14.51/6.11  tff(c_9190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9189, c_9185])).
% 14.51/6.11  tff(c_9192, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_9146])).
% 14.51/6.11  tff(c_9201, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_5'))=k2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9192, c_3244])).
% 14.51/6.11  tff(c_11054, plain, (![A_661, A_662]: (k2_funct_1(k5_relat_1(A_661, k2_funct_1(A_662)))=k5_relat_1(A_662, k2_funct_1(A_661)) | ~v2_funct_1(k2_funct_1(A_662)) | ~v2_funct_1(A_661) | ~v1_funct_1(k2_funct_1(A_662)) | ~v1_relat_1(k2_funct_1(A_662)) | ~v1_funct_1(A_661) | ~v1_relat_1(A_661) | ~v2_funct_1(A_662) | ~v1_funct_1(A_662) | ~v1_relat_1(A_662))), inference(superposition, [status(thm), theory('equality')], [c_40, c_605])).
% 14.51/6.11  tff(c_11111, plain, (k5_relat_1('#skF_5', k2_funct_1(k6_partfun1('#skF_2')))=k2_funct_1(k2_funct_1('#skF_5')) | ~v2_funct_1(k2_funct_1('#skF_5')) | ~v2_funct_1(k6_partfun1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v1_funct_1(k6_partfun1('#skF_2')) | ~v1_relat_1(k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9201, c_11054])).
% 14.51/6.11  tff(c_11145, plain, (k5_relat_1('#skF_5', k6_partfun1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_5')) | ~v2_funct_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_94, c_3235, c_105, c_9108, c_3245, c_9078, c_104, c_102, c_11111])).
% 14.51/6.11  tff(c_11160, plain, (~v2_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_11145])).
% 14.51/6.11  tff(c_11163, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_11160])).
% 14.51/6.11  tff(c_11167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_94, c_3235, c_11163])).
% 14.51/6.11  tff(c_11168, plain, (k5_relat_1('#skF_5', k6_partfun1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_11145])).
% 14.51/6.11  tff(c_6164, plain, (v1_relat_1(k5_relat_1('#skF_5', k6_partfun1(k1_relat_1('#skF_4'))))), inference(splitRight, [status(thm)], [c_3618])).
% 14.51/6.11  tff(c_9196, plain, (v1_relat_1(k5_relat_1('#skF_5', k6_partfun1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_9192, c_6164])).
% 14.51/6.11  tff(c_9079, plain, (v1_funct_1(k5_relat_1('#skF_5', k6_partfun1(k1_relat_1('#skF_4'))))), inference(splitRight, [status(thm)], [c_6163])).
% 14.51/6.11  tff(c_9195, plain, (v1_funct_1(k5_relat_1('#skF_5', k6_partfun1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_9192, c_9079])).
% 14.51/6.11  tff(c_9197, plain, (k2_funct_1(k5_relat_1('#skF_5', k6_partfun1('#skF_2')))=k2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9192, c_3575])).
% 14.51/6.11  tff(c_9389, plain, (v2_funct_1(k2_funct_1('#skF_5')) | ~v2_funct_1(k5_relat_1('#skF_5', k6_partfun1('#skF_2'))) | ~v1_funct_1(k5_relat_1('#skF_5', k6_partfun1('#skF_2'))) | ~v1_relat_1(k5_relat_1('#skF_5', k6_partfun1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_9197, c_28])).
% 14.51/6.11  tff(c_9417, plain, (v2_funct_1(k2_funct_1('#skF_5')) | ~v2_funct_1(k5_relat_1('#skF_5', k6_partfun1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_9196, c_9195, c_9389])).
% 14.51/6.11  tff(c_9437, plain, (~v2_funct_1(k5_relat_1('#skF_5', k6_partfun1('#skF_2')))), inference(splitLeft, [status(thm)], [c_9417])).
% 14.51/6.11  tff(c_11170, plain, (~v2_funct_1(k2_funct_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_11168, c_9437])).
% 14.51/6.11  tff(c_11204, plain, (~v2_funct_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_40, c_11170])).
% 14.51/6.11  tff(c_11210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_94, c_3235, c_3235, c_11204])).
% 14.51/6.11  tff(c_11211, plain, (v2_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_9417])).
% 14.51/6.11  tff(c_9191, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_9146])).
% 14.51/6.11  tff(c_11212, plain, (v2_funct_1(k5_relat_1('#skF_5', k6_partfun1('#skF_2')))), inference(splitRight, [status(thm)], [c_9417])).
% 14.51/6.11  tff(c_9386, plain, (k5_relat_1('#skF_5', k6_partfun1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_5')) | ~v2_funct_1(k5_relat_1('#skF_5', k6_partfun1('#skF_2'))) | ~v1_funct_1(k5_relat_1('#skF_5', k6_partfun1('#skF_2'))) | ~v1_relat_1(k5_relat_1('#skF_5', k6_partfun1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_9197, c_40])).
% 14.51/6.11  tff(c_9415, plain, (k5_relat_1('#skF_5', k6_partfun1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_5')) | ~v2_funct_1(k5_relat_1('#skF_5', k6_partfun1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_9196, c_9195, c_9386])).
% 14.51/6.11  tff(c_11660, plain, (k5_relat_1('#skF_5', k6_partfun1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_11212, c_9415])).
% 14.51/6.11  tff(c_14, plain, (![A_7]: (k1_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_50])).
% 14.51/6.11  tff(c_108, plain, (![A_7]: (k1_relat_1(k6_partfun1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_14])).
% 14.51/6.11  tff(c_12, plain, (![B_6, A_4]: (k2_relat_1(k5_relat_1(B_6, A_4))=k2_relat_1(A_4) | ~r1_tarski(k1_relat_1(A_4), k2_relat_1(B_6)) | ~v1_relat_1(B_6) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.51/6.11  tff(c_1819, plain, (![A_4]: (k2_relat_1(k5_relat_1('#skF_5', A_4))=k2_relat_1(A_4) | ~r1_tarski(k1_relat_1(A_4), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_4))), inference(superposition, [status(thm), theory('equality')], [c_1809, c_12])).
% 14.51/6.11  tff(c_3246, plain, (![A_299]: (k2_relat_1(k5_relat_1('#skF_5', A_299))=k2_relat_1(A_299) | ~r1_tarski(k1_relat_1(A_299), k1_relat_1('#skF_4')) | ~v1_relat_1(A_299))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_1819])).
% 14.51/6.11  tff(c_3252, plain, (![A_7]: (k2_relat_1(k5_relat_1('#skF_5', k6_partfun1(A_7)))=k2_relat_1(k6_partfun1(A_7)) | ~r1_tarski(A_7, k1_relat_1('#skF_4')) | ~v1_relat_1(k6_partfun1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_3246])).
% 14.51/6.11  tff(c_3258, plain, (![A_7]: (k2_relat_1(k5_relat_1('#skF_5', k6_partfun1(A_7)))=A_7 | ~r1_tarski(A_7, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_107, c_3252])).
% 14.51/6.11  tff(c_9200, plain, (![A_7]: (k2_relat_1(k5_relat_1('#skF_5', k6_partfun1(A_7)))=A_7 | ~r1_tarski(A_7, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_9192, c_3258])).
% 14.51/6.11  tff(c_11668, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_5')))='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11660, c_9200])).
% 14.51/6.11  tff(c_11675, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_5')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_11668])).
% 14.51/6.11  tff(c_11714, plain, (k1_relat_1(k2_funct_1('#skF_5'))='#skF_2' | ~v2_funct_1(k2_funct_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_11675, c_34])).
% 14.51/6.11  tff(c_11734, plain, (k1_relat_1(k2_funct_1('#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3245, c_9078, c_11211, c_11714])).
% 14.51/6.11  tff(c_1827, plain, (![A_4]: (k2_relat_1(k5_relat_1('#skF_5', A_4))=k2_relat_1(A_4) | ~r1_tarski(k1_relat_1(A_4), k1_relat_1('#skF_4')) | ~v1_relat_1(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_1819])).
% 14.51/6.11  tff(c_9202, plain, (![A_4]: (k2_relat_1(k5_relat_1('#skF_5', A_4))=k2_relat_1(A_4) | ~r1_tarski(k1_relat_1(A_4), '#skF_2') | ~v1_relat_1(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_9192, c_1827])).
% 14.51/6.11  tff(c_11743, plain, (k2_relat_1(k5_relat_1('#skF_5', k2_funct_1('#skF_5')))=k2_relat_1(k2_funct_1('#skF_5')) | ~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_11734, c_9202])).
% 14.51/6.11  tff(c_11762, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3245, c_10, c_107, c_9191, c_11743])).
% 14.51/6.11  tff(c_11792, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_11762, c_34])).
% 14.51/6.11  tff(c_11809, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_197, c_94, c_3235, c_11792])).
% 14.51/6.11  tff(c_11843, plain, (k5_relat_1(k6_partfun1('#skF_3'), '#skF_5')='#skF_5' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_11809, c_106])).
% 14.51/6.11  tff(c_11853, plain, (k5_relat_1(k6_partfun1('#skF_3'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_197, c_11843])).
% 14.51/6.11  tff(c_11663, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_11660, c_9196])).
% 14.51/6.11  tff(c_11664, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_11660, c_9195])).
% 14.51/6.11  tff(c_11661, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_11660, c_11212])).
% 14.51/6.11  tff(c_11662, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_5')))=k2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11660, c_9197])).
% 14.51/6.11  tff(c_11894, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_5')))=k2_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_11662, c_34])).
% 14.51/6.11  tff(c_11934, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_5')))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11663, c_11664, c_11661, c_11762, c_11894])).
% 14.51/6.11  tff(c_11971, plain, (k5_relat_1(k6_partfun1('#skF_3'), k2_funct_1(k2_funct_1('#skF_5')))=k2_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_11934, c_106])).
% 14.51/6.11  tff(c_11989, plain, (k5_relat_1(k6_partfun1('#skF_3'), k2_funct_1(k2_funct_1('#skF_5')))=k2_funct_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_11663, c_11971])).
% 14.51/6.11  tff(c_12133, plain, (k5_relat_1(k6_partfun1('#skF_3'), '#skF_5')=k2_funct_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_40, c_11989])).
% 14.51/6.11  tff(c_12146, plain, (k2_funct_1(k2_funct_1('#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_197, c_94, c_3235, c_11853, c_12133])).
% 14.51/6.11  tff(c_14528, plain, (![A_762, B_763]: (k2_funct_1(k2_funct_1(A_762))=B_763 | k5_relat_1(B_763, k2_funct_1(A_762))!=k6_partfun1(k1_relat_1(A_762)) | k2_relat_1(B_763)!=k1_relat_1(k2_funct_1(A_762)) | ~v2_funct_1(k2_funct_1(A_762)) | ~v1_funct_1(B_763) | ~v1_relat_1(B_763) | ~v1_funct_1(k2_funct_1(A_762)) | ~v1_relat_1(k2_funct_1(A_762)) | ~v2_funct_1(A_762) | ~v1_funct_1(A_762) | ~v1_relat_1(A_762))), inference(superposition, [status(thm), theory('equality')], [c_34, c_676])).
% 14.51/6.11  tff(c_14542, plain, (![B_763]: (k2_funct_1(k2_funct_1(k2_funct_1('#skF_5')))=B_763 | k6_partfun1(k1_relat_1(k2_funct_1('#skF_5')))!=k5_relat_1(B_763, '#skF_5') | k2_relat_1(B_763)!=k1_relat_1(k2_funct_1(k2_funct_1('#skF_5'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(B_763) | ~v1_relat_1(B_763) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_5'))) | ~v2_funct_1(k2_funct_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_12146, c_14528])).
% 14.51/6.11  tff(c_19169, plain, (![B_852]: (k2_funct_1('#skF_5')=B_852 | k5_relat_1(B_852, '#skF_5')!=k6_partfun1('#skF_2') | k2_relat_1(B_852)!='#skF_3' | ~v1_funct_1(B_852) | ~v1_relat_1(B_852))), inference(demodulation, [status(thm), theory('equality')], [c_3245, c_9078, c_11211, c_197, c_12146, c_94, c_12146, c_3235, c_12146, c_11809, c_12146, c_11734, c_12146, c_14542])).
% 14.51/6.11  tff(c_19292, plain, (k2_funct_1('#skF_5')='#skF_4' | k5_relat_1('#skF_4', '#skF_5')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_3' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_196, c_19169])).
% 14.51/6.11  tff(c_19404, plain, (k2_funct_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_326, c_11452, c_19292])).
% 14.51/6.11  tff(c_19419, plain, (k2_funct_1('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_19404, c_12146])).
% 14.51/6.11  tff(c_19430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_19419])).
% 14.51/6.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.51/6.11  
% 14.51/6.11  Inference rules
% 14.51/6.11  ----------------------
% 14.51/6.11  #Ref     : 0
% 14.51/6.11  #Sup     : 4356
% 14.51/6.11  #Fact    : 0
% 14.51/6.11  #Define  : 0
% 14.51/6.11  #Split   : 82
% 14.51/6.11  #Chain   : 0
% 14.51/6.11  #Close   : 0
% 14.51/6.11  
% 14.51/6.11  Ordering : KBO
% 14.51/6.11  
% 14.51/6.11  Simplification rules
% 14.51/6.11  ----------------------
% 14.51/6.11  #Subsume      : 336
% 14.51/6.11  #Demod        : 8010
% 14.51/6.11  #Tautology    : 1371
% 14.51/6.11  #SimpNegUnit  : 190
% 14.51/6.11  #BackRed      : 186
% 14.51/6.11  
% 14.51/6.11  #Partial instantiations: 0
% 14.51/6.11  #Strategies tried      : 1
% 14.51/6.11  
% 14.51/6.11  Timing (in seconds)
% 14.51/6.11  ----------------------
% 14.65/6.12  Preprocessing        : 0.63
% 14.65/6.12  Parsing              : 0.32
% 14.65/6.12  CNF conversion       : 0.05
% 14.65/6.12  Main loop            : 4.51
% 14.65/6.12  Inferencing          : 1.15
% 14.65/6.12  Reduction            : 2.13
% 14.65/6.12  Demodulation         : 1.75
% 14.65/6.12  BG Simplification    : 0.13
% 14.65/6.12  Subsumption          : 0.87
% 14.65/6.12  Abstraction          : 0.16
% 14.65/6.12  MUC search           : 0.00
% 14.65/6.12  Cooper               : 0.00
% 14.65/6.12  Total                : 5.26
% 14.65/6.12  Index Insertion      : 0.00
% 14.65/6.12  Index Deletion       : 0.00
% 14.65/6.12  Index Matching       : 0.00
% 14.65/6.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
