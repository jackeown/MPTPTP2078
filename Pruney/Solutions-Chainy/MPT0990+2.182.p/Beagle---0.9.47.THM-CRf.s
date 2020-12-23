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
% DateTime   : Thu Dec  3 10:13:23 EST 2020

% Result     : Theorem 9.01s
% Output     : CNFRefutation 9.31s
% Verified   : 
% Statistics : Number of formulae       :  192 (2019 expanded)
%              Number of leaves         :   54 ( 728 expanded)
%              Depth                    :   25
%              Number of atoms          :  443 (6749 expanded)
%              Number of equality atoms :  149 (2448 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_297,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_202,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_145,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_166,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_32,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_261,axiom,(
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

tff(f_190,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_174,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_186,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_219,axiom,(
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

tff(f_245,axiom,(
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

tff(f_135,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_125,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_200,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_102,plain,(
    k2_funct_1('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_12,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_120,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_277,plain,(
    ! [B_92,A_93] :
      ( v1_relat_1(B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_93))
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_286,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_120,c_277])).

tff(c_295,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_286])).

tff(c_124,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_30,plain,(
    ! [A_21] :
      ( v1_relat_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_108,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_80,plain,(
    ! [A_54] : k6_relat_1(A_54) = k6_partfun1(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_36,plain,(
    ! [A_23] : v1_relat_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_129,plain,(
    ! [A_23] : v1_relat_1(k6_partfun1(A_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_36])).

tff(c_20,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_135,plain,(
    ! [A_18] : k1_relat_1(k6_partfun1(A_18)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_20])).

tff(c_24,plain,(
    ! [A_19] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_19)),A_19) = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_231,plain,(
    ! [A_88] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_88)),A_88) = A_88
      | ~ v1_relat_1(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_24])).

tff(c_240,plain,(
    ! [A_18] :
      ( k5_relat_1(k6_partfun1(A_18),k6_partfun1(A_18)) = k6_partfun1(A_18)
      | ~ v1_relat_1(k6_partfun1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_231])).

tff(c_244,plain,(
    ! [A_18] : k5_relat_1(k6_partfun1(A_18),k6_partfun1(A_18)) = k6_partfun1(A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_240])).

tff(c_58,plain,(
    ! [A_29] :
      ( k5_relat_1(A_29,k2_funct_1(A_29)) = k6_relat_1(k1_relat_1(A_29))
      | ~ v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_126,plain,(
    ! [A_29] :
      ( k5_relat_1(A_29,k2_funct_1(A_29)) = k6_partfun1(k1_relat_1(A_29))
      | ~ v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_58])).

tff(c_112,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_409,plain,(
    ! [A_106,B_107,C_108] :
      ( k2_relset_1(A_106,B_107,C_108) = k2_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_418,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_409])).

tff(c_423,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_418])).

tff(c_26,plain,(
    ! [A_20] :
      ( k5_relat_1(A_20,k6_relat_1(k2_relat_1(A_20))) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_132,plain,(
    ! [A_20] :
      ( k5_relat_1(A_20,k6_partfun1(k2_relat_1(A_20))) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_26])).

tff(c_433,plain,
    ( k5_relat_1('#skF_4',k6_partfun1('#skF_3')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_132])).

tff(c_441,plain,(
    k5_relat_1('#skF_4',k6_partfun1('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_433])).

tff(c_133,plain,(
    ! [A_19] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_19)),A_19) = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_24])).

tff(c_721,plain,(
    ! [A_121,B_122,C_123] :
      ( k5_relat_1(k5_relat_1(A_121,B_122),C_123) = k5_relat_1(A_121,k5_relat_1(B_122,C_123))
      | ~ v1_relat_1(C_123)
      | ~ v1_relat_1(B_122)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_775,plain,(
    ! [A_19,C_123] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_19)),k5_relat_1(A_19,C_123)) = k5_relat_1(A_19,C_123)
      | ~ v1_relat_1(C_123)
      | ~ v1_relat_1(A_19)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_19)))
      | ~ v1_relat_1(A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_721])).

tff(c_2119,plain,(
    ! [A_177,C_178] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_177)),k5_relat_1(A_177,C_178)) = k5_relat_1(A_177,C_178)
      | ~ v1_relat_1(C_178)
      | ~ v1_relat_1(A_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_775])).

tff(c_2161,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),'#skF_4') = k5_relat_1('#skF_4',k6_partfun1('#skF_3'))
    | ~ v1_relat_1(k6_partfun1('#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_2119])).

tff(c_2192,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_129,c_441,c_2161])).

tff(c_18,plain,(
    ! [A_11,B_15,C_17] :
      ( k5_relat_1(k5_relat_1(A_11,B_15),C_17) = k5_relat_1(A_11,k5_relat_1(B_15,C_17))
      | ~ v1_relat_1(C_17)
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2210,plain,(
    ! [C_17] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k5_relat_1('#skF_4',C_17)) = k5_relat_1('#skF_4',C_17)
      | ~ v1_relat_1(C_17)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(k6_partfun1(k1_relat_1('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2192,c_18])).

tff(c_2281,plain,(
    ! [C_180] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k5_relat_1('#skF_4',C_180)) = k5_relat_1('#skF_4',C_180)
      | ~ v1_relat_1(C_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_295,c_2210])).

tff(c_2314,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k6_partfun1(k1_relat_1('#skF_4'))) = k5_relat_1('#skF_4',k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_2281])).

tff(c_2338,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_124,c_108,c_244,c_2314])).

tff(c_2343,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2338])).

tff(c_2346,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_2343])).

tff(c_2350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_124,c_2346])).

tff(c_2352,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2338])).

tff(c_114,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_283,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_114,c_277])).

tff(c_292,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_283])).

tff(c_6,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_140,plain,(
    ! [A_76] :
      ( k1_xboole_0 = A_76
      | ~ v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_148,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_140])).

tff(c_106,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_166,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_106])).

tff(c_118,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_116,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_421,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_114,c_409])).

tff(c_92,plain,(
    ! [B_67,C_68,A_66] :
      ( k6_partfun1(B_67) = k5_relat_1(k2_funct_1(C_68),C_68)
      | k1_xboole_0 = B_67
      | ~ v2_funct_1(C_68)
      | k2_relset_1(A_66,B_67,C_68) != B_67
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ v1_funct_2(C_68,A_66,B_67)
      | ~ v1_funct_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_2859,plain,(
    ! [B_206,C_207,A_208] :
      ( k6_partfun1(B_206) = k5_relat_1(k2_funct_1(C_207),C_207)
      | B_206 = '#skF_1'
      | ~ v2_funct_1(C_207)
      | k2_relset_1(A_208,B_206,C_207) != B_206
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_208,B_206)))
      | ~ v1_funct_2(C_207,A_208,B_206)
      | ~ v1_funct_1(C_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_92])).

tff(c_2867,plain,
    ( k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_2','#skF_5') != '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_114,c_2859])).

tff(c_2880,plain,
    ( k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5')
    | k2_relat_1('#skF_5') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_116,c_421,c_2867])).

tff(c_2881,plain,
    ( k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_5')
    | k2_relat_1('#skF_5') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_2880])).

tff(c_2937,plain,(
    k2_relat_1('#skF_5') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2881])).

tff(c_122,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_76,plain,(
    ! [A_47] : m1_subset_1(k6_partfun1(A_47),k1_zfmisc_1(k2_zfmisc_1(A_47,A_47))) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_352,plain,(
    ! [A_100,B_101,D_102] :
      ( r2_relset_1(A_100,B_101,D_102,D_102)
      | ~ m1_subset_1(D_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_359,plain,(
    ! [A_47] : r2_relset_1(A_47,A_47,k6_partfun1(A_47),k6_partfun1(A_47)) ),
    inference(resolution,[status(thm)],[c_76,c_352])).

tff(c_2070,plain,(
    ! [C_173,A_172,E_171,D_174,B_176,F_175] :
      ( m1_subset_1(k1_partfun1(A_172,B_176,C_173,D_174,E_171,F_175),k1_zfmisc_1(k2_zfmisc_1(A_172,D_174)))
      | ~ m1_subset_1(F_175,k1_zfmisc_1(k2_zfmisc_1(C_173,D_174)))
      | ~ v1_funct_1(F_175)
      | ~ m1_subset_1(E_171,k1_zfmisc_1(k2_zfmisc_1(A_172,B_176)))
      | ~ v1_funct_1(E_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_110,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_790,plain,(
    ! [D_124,C_125,A_126,B_127] :
      ( D_124 = C_125
      | ~ r2_relset_1(A_126,B_127,C_125,D_124)
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_802,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_110,c_790])).

tff(c_823,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_802])).

tff(c_988,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_823])).

tff(c_2090,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2070,c_988])).

tff(c_2109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_120,c_118,c_114,c_2090])).

tff(c_2110,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_823])).

tff(c_3712,plain,(
    ! [A_238,B_239,C_240,D_241] :
      ( k2_relset_1(A_238,B_239,C_240) = B_239
      | ~ r2_relset_1(B_239,B_239,k1_partfun1(B_239,A_238,A_238,B_239,D_241,C_240),k6_partfun1(B_239))
      | ~ m1_subset_1(D_241,k1_zfmisc_1(k2_zfmisc_1(B_239,A_238)))
      | ~ v1_funct_2(D_241,B_239,A_238)
      | ~ v1_funct_1(D_241)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239)))
      | ~ v1_funct_2(C_240,A_238,B_239)
      | ~ v1_funct_1(C_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_3718,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2110,c_3712])).

tff(c_3722,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_116,c_114,c_124,c_122,c_120,c_359,c_421,c_3718])).

tff(c_3724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2937,c_3722])).

tff(c_3726,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2881])).

tff(c_3752,plain,
    ( k5_relat_1('#skF_5',k6_partfun1('#skF_2')) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3726,c_132])).

tff(c_3770,plain,(
    k5_relat_1('#skF_5',k6_partfun1('#skF_2')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_3752])).

tff(c_104,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_165,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_104])).

tff(c_2351,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2338])).

tff(c_94,plain,(
    ! [A_66,C_68,B_67] :
      ( k6_partfun1(A_66) = k5_relat_1(C_68,k2_funct_1(C_68))
      | k1_xboole_0 = B_67
      | ~ v2_funct_1(C_68)
      | k2_relset_1(A_66,B_67,C_68) != B_67
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ v1_funct_2(C_68,A_66,B_67)
      | ~ v1_funct_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_3856,plain,(
    ! [A_245,C_246,B_247] :
      ( k6_partfun1(A_245) = k5_relat_1(C_246,k2_funct_1(C_246))
      | B_247 = '#skF_1'
      | ~ v2_funct_1(C_246)
      | k2_relset_1(A_245,B_247,C_246) != B_247
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_245,B_247)))
      | ~ v1_funct_2(C_246,A_245,B_247)
      | ~ v1_funct_1(C_246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_94])).

tff(c_3866,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_3856])).

tff(c_3881,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_112,c_108,c_2351,c_3866])).

tff(c_3882,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_3881])).

tff(c_3886,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3882,c_2351])).

tff(c_3727,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3726,c_421])).

tff(c_3864,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_2','#skF_5') != '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_114,c_3856])).

tff(c_3877,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_116,c_3727,c_3864])).

tff(c_3878,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | ~ v2_funct_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_3877])).

tff(c_4045,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3878])).

tff(c_38,plain,(
    ! [A_23] : v2_funct_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_128,plain,(
    ! [A_23] : v2_funct_1(k6_partfun1(A_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_38])).

tff(c_86,plain,(
    ! [D_63,A_60,C_62,E_65,B_61] :
      ( k1_xboole_0 = C_62
      | v2_funct_1(E_65)
      | k2_relset_1(A_60,B_61,D_63) != B_61
      | ~ v2_funct_1(k1_partfun1(A_60,B_61,B_61,C_62,D_63,E_65))
      | ~ m1_subset_1(E_65,k1_zfmisc_1(k2_zfmisc_1(B_61,C_62)))
      | ~ v1_funct_2(E_65,B_61,C_62)
      | ~ v1_funct_1(E_65)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ v1_funct_2(D_63,A_60,B_61)
      | ~ v1_funct_1(D_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_4535,plain,(
    ! [A_272,C_269,D_270,E_273,B_271] :
      ( C_269 = '#skF_1'
      | v2_funct_1(E_273)
      | k2_relset_1(A_272,B_271,D_270) != B_271
      | ~ v2_funct_1(k1_partfun1(A_272,B_271,B_271,C_269,D_270,E_273))
      | ~ m1_subset_1(E_273,k1_zfmisc_1(k2_zfmisc_1(B_271,C_269)))
      | ~ v1_funct_2(E_273,B_271,C_269)
      | ~ v1_funct_1(E_273)
      | ~ m1_subset_1(D_270,k1_zfmisc_1(k2_zfmisc_1(A_272,B_271)))
      | ~ v1_funct_2(D_270,A_272,B_271)
      | ~ v1_funct_1(D_270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_86])).

tff(c_4539,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_2110,c_4535])).

tff(c_4544,plain,
    ( '#skF_2' = '#skF_1'
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_120,c_118,c_116,c_114,c_128,c_112,c_4539])).

tff(c_4546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4045,c_166,c_4544])).

tff(c_4548,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_3878])).

tff(c_22,plain,(
    ! [A_18] : k2_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_134,plain,(
    ! [A_18] : k2_relat_1(k6_partfun1(A_18)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_22])).

tff(c_4547,plain,(
    k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3878])).

tff(c_52,plain,(
    ! [A_28] :
      ( k2_relat_1(k5_relat_1(A_28,k2_funct_1(A_28))) = k1_relat_1(A_28)
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_4643,plain,
    ( k2_relat_1(k6_partfun1('#skF_3')) = k1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4547,c_52])).

tff(c_4660,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_118,c_4548,c_134,c_4643])).

tff(c_363,plain,(
    ! [A_104] :
      ( k2_relat_1(k2_funct_1(A_104)) = k1_relat_1(A_104)
      | ~ v2_funct_1(A_104)
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_16,plain,(
    ! [A_10] :
      ( k10_relat_1(A_10,k2_relat_1(A_10)) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7946,plain,(
    ! [A_365] :
      ( k10_relat_1(k2_funct_1(A_365),k1_relat_1(A_365)) = k1_relat_1(k2_funct_1(A_365))
      | ~ v1_relat_1(k2_funct_1(A_365))
      | ~ v2_funct_1(A_365)
      | ~ v1_funct_1(A_365)
      | ~ v1_relat_1(A_365) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_16])).

tff(c_7958,plain,
    ( k10_relat_1(k2_funct_1('#skF_5'),'#skF_3') = k1_relat_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4660,c_7946])).

tff(c_7978,plain,
    ( k10_relat_1(k2_funct_1('#skF_5'),'#skF_3') = k1_relat_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_118,c_4548,c_7958])).

tff(c_7989,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_7978])).

tff(c_7992,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_7989])).

tff(c_7996,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_118,c_7992])).

tff(c_7998,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_7978])).

tff(c_386,plain,(
    ! [A_105] :
      ( k1_relat_1(k2_funct_1(A_105)) = k2_relat_1(A_105)
      | ~ v2_funct_1(A_105)
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_8339,plain,(
    ! [A_379] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_379)),k2_funct_1(A_379)) = k2_funct_1(A_379)
      | ~ v1_relat_1(k2_funct_1(A_379))
      | ~ v2_funct_1(A_379)
      | ~ v1_funct_1(A_379)
      | ~ v1_relat_1(A_379) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_133])).

tff(c_8373,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_5')) = k2_funct_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3726,c_8339])).

tff(c_8401,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_5')) = k2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_118,c_4548,c_7998,c_8373])).

tff(c_2773,plain,(
    ! [D_196,F_195,C_199,E_200,A_198,B_197] :
      ( k1_partfun1(A_198,B_197,C_199,D_196,E_200,F_195) = k5_relat_1(E_200,F_195)
      | ~ m1_subset_1(F_195,k1_zfmisc_1(k2_zfmisc_1(C_199,D_196)))
      | ~ v1_funct_1(F_195)
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_197)))
      | ~ v1_funct_1(E_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_2781,plain,(
    ! [A_198,B_197,E_200] :
      ( k1_partfun1(A_198,B_197,'#skF_3','#skF_2',E_200,'#skF_5') = k5_relat_1(E_200,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_197)))
      | ~ v1_funct_1(E_200) ) ),
    inference(resolution,[status(thm)],[c_114,c_2773])).

tff(c_3776,plain,(
    ! [A_242,B_243,E_244] :
      ( k1_partfun1(A_242,B_243,'#skF_3','#skF_2',E_244,'#skF_5') = k5_relat_1(E_244,'#skF_5')
      | ~ m1_subset_1(E_244,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243)))
      | ~ v1_funct_1(E_244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_2781])).

tff(c_3791,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_3776])).

tff(c_3804,plain,(
    k5_relat_1('#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_2110,c_3791])).

tff(c_3817,plain,(
    ! [C_17] :
      ( k5_relat_1(k6_partfun1('#skF_2'),C_17) = k5_relat_1('#skF_4',k5_relat_1('#skF_5',C_17))
      | ~ v1_relat_1(C_17)
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3804,c_18])).

tff(c_3827,plain,(
    ! [C_17] :
      ( k5_relat_1(k6_partfun1('#skF_2'),C_17) = k5_relat_1('#skF_4',k5_relat_1('#skF_5',C_17))
      | ~ v1_relat_1(C_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_292,c_3817])).

tff(c_8414,plain,
    ( k5_relat_1('#skF_4',k5_relat_1('#skF_5',k2_funct_1('#skF_5'))) = k2_funct_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8401,c_3827])).

tff(c_8438,plain,(
    k2_funct_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7998,c_441,c_4547,c_8414])).

tff(c_8456,plain,(
    k5_relat_1('#skF_5','#skF_4') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8438,c_4547])).

tff(c_8628,plain,(
    ! [C_17] :
      ( k5_relat_1(k6_partfun1('#skF_3'),C_17) = k5_relat_1('#skF_5',k5_relat_1('#skF_4',C_17))
      | ~ v1_relat_1(C_17)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8456,c_18])).

tff(c_9396,plain,(
    ! [C_398] :
      ( k5_relat_1(k6_partfun1('#skF_3'),C_398) = k5_relat_1('#skF_5',k5_relat_1('#skF_4',C_398))
      | ~ v1_relat_1(C_398) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_295,c_8628])).

tff(c_8379,plain,
    ( k5_relat_1(k6_partfun1('#skF_3'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_8339])).

tff(c_8403,plain,(
    k5_relat_1(k6_partfun1('#skF_3'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_124,c_108,c_2352,c_8379])).

tff(c_9406,plain,
    ( k5_relat_1('#skF_5',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9396,c_8403])).

tff(c_9507,plain,(
    k2_funct_1('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2352,c_3770,c_3886,c_9406])).

tff(c_9509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_9507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.01/3.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.01/3.17  
% 9.01/3.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.01/3.18  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.01/3.18  
% 9.01/3.18  %Foreground sorts:
% 9.01/3.18  
% 9.01/3.18  
% 9.01/3.18  %Background operators:
% 9.01/3.18  
% 9.01/3.18  
% 9.01/3.18  %Foreground operators:
% 9.01/3.18  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.01/3.18  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 9.01/3.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.01/3.18  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.01/3.18  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.01/3.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.01/3.18  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.01/3.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.01/3.18  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.01/3.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.01/3.18  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.01/3.18  tff('#skF_5', type, '#skF_5': $i).
% 9.01/3.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.01/3.18  tff('#skF_2', type, '#skF_2': $i).
% 9.01/3.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.01/3.18  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.01/3.18  tff('#skF_3', type, '#skF_3': $i).
% 9.01/3.18  tff('#skF_1', type, '#skF_1': $i).
% 9.01/3.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.01/3.18  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.01/3.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.01/3.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.01/3.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.01/3.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.01/3.18  tff('#skF_4', type, '#skF_4': $i).
% 9.01/3.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.01/3.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.01/3.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.01/3.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.01/3.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.01/3.18  
% 9.01/3.20  tff(f_297, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 9.01/3.20  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.01/3.20  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.01/3.20  tff(f_87, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.01/3.20  tff(f_202, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.01/3.20  tff(f_95, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 9.01/3.20  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 9.01/3.20  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 9.01/3.20  tff(f_145, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 9.01/3.20  tff(f_166, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.01/3.20  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 9.01/3.20  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 9.01/3.20  tff(f_32, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 9.01/3.20  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.01/3.20  tff(f_261, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 9.01/3.20  tff(f_190, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.01/3.20  tff(f_174, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.01/3.20  tff(f_186, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.01/3.20  tff(f_219, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 9.01/3.20  tff(f_245, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 9.01/3.20  tff(f_135, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 9.01/3.20  tff(f_125, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 9.01/3.20  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 9.01/3.20  tff(f_200, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.01/3.20  tff(c_102, plain, (k2_funct_1('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_297])).
% 9.01/3.20  tff(c_12, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.01/3.20  tff(c_120, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_297])).
% 9.01/3.20  tff(c_277, plain, (![B_92, A_93]: (v1_relat_1(B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(A_93)) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.01/3.20  tff(c_286, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_120, c_277])).
% 9.01/3.20  tff(c_295, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_286])).
% 9.01/3.20  tff(c_124, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_297])).
% 9.01/3.20  tff(c_30, plain, (![A_21]: (v1_relat_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.01/3.20  tff(c_108, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_297])).
% 9.01/3.20  tff(c_80, plain, (![A_54]: (k6_relat_1(A_54)=k6_partfun1(A_54))), inference(cnfTransformation, [status(thm)], [f_202])).
% 9.01/3.20  tff(c_36, plain, (![A_23]: (v1_relat_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.01/3.20  tff(c_129, plain, (![A_23]: (v1_relat_1(k6_partfun1(A_23)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_36])).
% 9.01/3.20  tff(c_20, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.01/3.20  tff(c_135, plain, (![A_18]: (k1_relat_1(k6_partfun1(A_18))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_20])).
% 9.01/3.20  tff(c_24, plain, (![A_19]: (k5_relat_1(k6_relat_1(k1_relat_1(A_19)), A_19)=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.01/3.20  tff(c_231, plain, (![A_88]: (k5_relat_1(k6_partfun1(k1_relat_1(A_88)), A_88)=A_88 | ~v1_relat_1(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_24])).
% 9.01/3.20  tff(c_240, plain, (![A_18]: (k5_relat_1(k6_partfun1(A_18), k6_partfun1(A_18))=k6_partfun1(A_18) | ~v1_relat_1(k6_partfun1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_231])).
% 9.01/3.20  tff(c_244, plain, (![A_18]: (k5_relat_1(k6_partfun1(A_18), k6_partfun1(A_18))=k6_partfun1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_240])).
% 9.01/3.20  tff(c_58, plain, (![A_29]: (k5_relat_1(A_29, k2_funct_1(A_29))=k6_relat_1(k1_relat_1(A_29)) | ~v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_145])).
% 9.01/3.20  tff(c_126, plain, (![A_29]: (k5_relat_1(A_29, k2_funct_1(A_29))=k6_partfun1(k1_relat_1(A_29)) | ~v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_58])).
% 9.01/3.20  tff(c_112, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_297])).
% 9.01/3.20  tff(c_409, plain, (![A_106, B_107, C_108]: (k2_relset_1(A_106, B_107, C_108)=k2_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 9.01/3.20  tff(c_418, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_120, c_409])).
% 9.01/3.20  tff(c_423, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_418])).
% 9.01/3.20  tff(c_26, plain, (![A_20]: (k5_relat_1(A_20, k6_relat_1(k2_relat_1(A_20)))=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.01/3.20  tff(c_132, plain, (![A_20]: (k5_relat_1(A_20, k6_partfun1(k2_relat_1(A_20)))=A_20 | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_26])).
% 9.01/3.20  tff(c_433, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_3'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_423, c_132])).
% 9.01/3.20  tff(c_441, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_295, c_433])).
% 9.01/3.20  tff(c_133, plain, (![A_19]: (k5_relat_1(k6_partfun1(k1_relat_1(A_19)), A_19)=A_19 | ~v1_relat_1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_24])).
% 9.01/3.20  tff(c_721, plain, (![A_121, B_122, C_123]: (k5_relat_1(k5_relat_1(A_121, B_122), C_123)=k5_relat_1(A_121, k5_relat_1(B_122, C_123)) | ~v1_relat_1(C_123) | ~v1_relat_1(B_122) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.01/3.20  tff(c_775, plain, (![A_19, C_123]: (k5_relat_1(k6_partfun1(k1_relat_1(A_19)), k5_relat_1(A_19, C_123))=k5_relat_1(A_19, C_123) | ~v1_relat_1(C_123) | ~v1_relat_1(A_19) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_19))) | ~v1_relat_1(A_19))), inference(superposition, [status(thm), theory('equality')], [c_133, c_721])).
% 9.01/3.20  tff(c_2119, plain, (![A_177, C_178]: (k5_relat_1(k6_partfun1(k1_relat_1(A_177)), k5_relat_1(A_177, C_178))=k5_relat_1(A_177, C_178) | ~v1_relat_1(C_178) | ~v1_relat_1(A_177))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_775])).
% 9.01/3.20  tff(c_2161, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), '#skF_4')=k5_relat_1('#skF_4', k6_partfun1('#skF_3')) | ~v1_relat_1(k6_partfun1('#skF_3')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_441, c_2119])).
% 9.01/3.20  tff(c_2192, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_295, c_129, c_441, c_2161])).
% 9.01/3.20  tff(c_18, plain, (![A_11, B_15, C_17]: (k5_relat_1(k5_relat_1(A_11, B_15), C_17)=k5_relat_1(A_11, k5_relat_1(B_15, C_17)) | ~v1_relat_1(C_17) | ~v1_relat_1(B_15) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.01/3.20  tff(c_2210, plain, (![C_17]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k5_relat_1('#skF_4', C_17))=k5_relat_1('#skF_4', C_17) | ~v1_relat_1(C_17) | ~v1_relat_1('#skF_4') | ~v1_relat_1(k6_partfun1(k1_relat_1('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_2192, c_18])).
% 9.01/3.20  tff(c_2281, plain, (![C_180]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k5_relat_1('#skF_4', C_180))=k5_relat_1('#skF_4', C_180) | ~v1_relat_1(C_180))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_295, c_2210])).
% 9.01/3.20  tff(c_2314, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k6_partfun1(k1_relat_1('#skF_4')))=k5_relat_1('#skF_4', k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_126, c_2281])).
% 9.01/3.20  tff(c_2338, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_124, c_108, c_244, c_2314])).
% 9.01/3.20  tff(c_2343, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_2338])).
% 9.01/3.20  tff(c_2346, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_2343])).
% 9.01/3.20  tff(c_2350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_295, c_124, c_2346])).
% 9.01/3.20  tff(c_2352, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2338])).
% 9.01/3.20  tff(c_114, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_297])).
% 9.01/3.20  tff(c_283, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_114, c_277])).
% 9.01/3.20  tff(c_292, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_283])).
% 9.01/3.20  tff(c_6, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.01/3.20  tff(c_140, plain, (![A_76]: (k1_xboole_0=A_76 | ~v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_30])).
% 9.01/3.20  tff(c_148, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_6, c_140])).
% 9.01/3.20  tff(c_106, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_297])).
% 9.01/3.20  tff(c_166, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_106])).
% 9.01/3.20  tff(c_118, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_297])).
% 9.01/3.20  tff(c_116, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_297])).
% 9.01/3.20  tff(c_421, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_114, c_409])).
% 9.01/3.20  tff(c_92, plain, (![B_67, C_68, A_66]: (k6_partfun1(B_67)=k5_relat_1(k2_funct_1(C_68), C_68) | k1_xboole_0=B_67 | ~v2_funct_1(C_68) | k2_relset_1(A_66, B_67, C_68)!=B_67 | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~v1_funct_2(C_68, A_66, B_67) | ~v1_funct_1(C_68))), inference(cnfTransformation, [status(thm)], [f_261])).
% 9.01/3.20  tff(c_2859, plain, (![B_206, C_207, A_208]: (k6_partfun1(B_206)=k5_relat_1(k2_funct_1(C_207), C_207) | B_206='#skF_1' | ~v2_funct_1(C_207) | k2_relset_1(A_208, B_206, C_207)!=B_206 | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_208, B_206))) | ~v1_funct_2(C_207, A_208, B_206) | ~v1_funct_1(C_207))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_92])).
% 9.01/3.20  tff(c_2867, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_2') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_2', '#skF_5')!='#skF_2' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_114, c_2859])).
% 9.31/3.20  tff(c_2880, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_2') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5') | k2_relat_1('#skF_5')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_116, c_421, c_2867])).
% 9.31/3.20  tff(c_2881, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_5') | k2_relat_1('#skF_5')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_166, c_2880])).
% 9.31/3.20  tff(c_2937, plain, (k2_relat_1('#skF_5')!='#skF_2'), inference(splitLeft, [status(thm)], [c_2881])).
% 9.31/3.20  tff(c_122, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_297])).
% 9.31/3.20  tff(c_76, plain, (![A_47]: (m1_subset_1(k6_partfun1(A_47), k1_zfmisc_1(k2_zfmisc_1(A_47, A_47))))), inference(cnfTransformation, [status(thm)], [f_190])).
% 9.31/3.20  tff(c_352, plain, (![A_100, B_101, D_102]: (r2_relset_1(A_100, B_101, D_102, D_102) | ~m1_subset_1(D_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.31/3.20  tff(c_359, plain, (![A_47]: (r2_relset_1(A_47, A_47, k6_partfun1(A_47), k6_partfun1(A_47)))), inference(resolution, [status(thm)], [c_76, c_352])).
% 9.31/3.20  tff(c_2070, plain, (![C_173, A_172, E_171, D_174, B_176, F_175]: (m1_subset_1(k1_partfun1(A_172, B_176, C_173, D_174, E_171, F_175), k1_zfmisc_1(k2_zfmisc_1(A_172, D_174))) | ~m1_subset_1(F_175, k1_zfmisc_1(k2_zfmisc_1(C_173, D_174))) | ~v1_funct_1(F_175) | ~m1_subset_1(E_171, k1_zfmisc_1(k2_zfmisc_1(A_172, B_176))) | ~v1_funct_1(E_171))), inference(cnfTransformation, [status(thm)], [f_186])).
% 9.31/3.20  tff(c_110, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_297])).
% 9.31/3.20  tff(c_790, plain, (![D_124, C_125, A_126, B_127]: (D_124=C_125 | ~r2_relset_1(A_126, B_127, C_125, D_124) | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.31/3.20  tff(c_802, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_110, c_790])).
% 9.31/3.20  tff(c_823, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_802])).
% 9.31/3.20  tff(c_988, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_823])).
% 9.31/3.20  tff(c_2090, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_2070, c_988])).
% 9.31/3.20  tff(c_2109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_120, c_118, c_114, c_2090])).
% 9.31/3.20  tff(c_2110, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_823])).
% 9.31/3.20  tff(c_3712, plain, (![A_238, B_239, C_240, D_241]: (k2_relset_1(A_238, B_239, C_240)=B_239 | ~r2_relset_1(B_239, B_239, k1_partfun1(B_239, A_238, A_238, B_239, D_241, C_240), k6_partfun1(B_239)) | ~m1_subset_1(D_241, k1_zfmisc_1(k2_zfmisc_1(B_239, A_238))) | ~v1_funct_2(D_241, B_239, A_238) | ~v1_funct_1(D_241) | ~m1_subset_1(C_240, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))) | ~v1_funct_2(C_240, A_238, B_239) | ~v1_funct_1(C_240))), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.31/3.20  tff(c_3718, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2110, c_3712])).
% 9.31/3.20  tff(c_3722, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_116, c_114, c_124, c_122, c_120, c_359, c_421, c_3718])).
% 9.31/3.20  tff(c_3724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2937, c_3722])).
% 9.31/3.20  tff(c_3726, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(splitRight, [status(thm)], [c_2881])).
% 9.31/3.20  tff(c_3752, plain, (k5_relat_1('#skF_5', k6_partfun1('#skF_2'))='#skF_5' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3726, c_132])).
% 9.31/3.20  tff(c_3770, plain, (k5_relat_1('#skF_5', k6_partfun1('#skF_2'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_292, c_3752])).
% 9.31/3.20  tff(c_104, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_297])).
% 9.31/3.20  tff(c_165, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_104])).
% 9.31/3.20  tff(c_2351, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2338])).
% 9.31/3.20  tff(c_94, plain, (![A_66, C_68, B_67]: (k6_partfun1(A_66)=k5_relat_1(C_68, k2_funct_1(C_68)) | k1_xboole_0=B_67 | ~v2_funct_1(C_68) | k2_relset_1(A_66, B_67, C_68)!=B_67 | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~v1_funct_2(C_68, A_66, B_67) | ~v1_funct_1(C_68))), inference(cnfTransformation, [status(thm)], [f_261])).
% 9.31/3.20  tff(c_3856, plain, (![A_245, C_246, B_247]: (k6_partfun1(A_245)=k5_relat_1(C_246, k2_funct_1(C_246)) | B_247='#skF_1' | ~v2_funct_1(C_246) | k2_relset_1(A_245, B_247, C_246)!=B_247 | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_245, B_247))) | ~v1_funct_2(C_246, A_245, B_247) | ~v1_funct_1(C_246))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_94])).
% 9.31/3.20  tff(c_3866, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_120, c_3856])).
% 9.31/3.20  tff(c_3881, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_112, c_108, c_2351, c_3866])).
% 9.31/3.20  tff(c_3882, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_165, c_3881])).
% 9.31/3.20  tff(c_3886, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3882, c_2351])).
% 9.31/3.20  tff(c_3727, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3726, c_421])).
% 9.31/3.20  tff(c_3864, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_2', '#skF_5')!='#skF_2' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_114, c_3856])).
% 9.31/3.20  tff(c_3877, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_116, c_3727, c_3864])).
% 9.31/3.20  tff(c_3878, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | ~v2_funct_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_166, c_3877])).
% 9.31/3.20  tff(c_4045, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_3878])).
% 9.31/3.20  tff(c_38, plain, (![A_23]: (v2_funct_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.31/3.20  tff(c_128, plain, (![A_23]: (v2_funct_1(k6_partfun1(A_23)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_38])).
% 9.31/3.20  tff(c_86, plain, (![D_63, A_60, C_62, E_65, B_61]: (k1_xboole_0=C_62 | v2_funct_1(E_65) | k2_relset_1(A_60, B_61, D_63)!=B_61 | ~v2_funct_1(k1_partfun1(A_60, B_61, B_61, C_62, D_63, E_65)) | ~m1_subset_1(E_65, k1_zfmisc_1(k2_zfmisc_1(B_61, C_62))) | ~v1_funct_2(E_65, B_61, C_62) | ~v1_funct_1(E_65) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~v1_funct_2(D_63, A_60, B_61) | ~v1_funct_1(D_63))), inference(cnfTransformation, [status(thm)], [f_245])).
% 9.31/3.20  tff(c_4535, plain, (![A_272, C_269, D_270, E_273, B_271]: (C_269='#skF_1' | v2_funct_1(E_273) | k2_relset_1(A_272, B_271, D_270)!=B_271 | ~v2_funct_1(k1_partfun1(A_272, B_271, B_271, C_269, D_270, E_273)) | ~m1_subset_1(E_273, k1_zfmisc_1(k2_zfmisc_1(B_271, C_269))) | ~v1_funct_2(E_273, B_271, C_269) | ~v1_funct_1(E_273) | ~m1_subset_1(D_270, k1_zfmisc_1(k2_zfmisc_1(A_272, B_271))) | ~v1_funct_2(D_270, A_272, B_271) | ~v1_funct_1(D_270))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_86])).
% 9.31/3.20  tff(c_4539, plain, ('#skF_2'='#skF_1' | v2_funct_1('#skF_5') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2110, c_4535])).
% 9.31/3.20  tff(c_4544, plain, ('#skF_2'='#skF_1' | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_120, c_118, c_116, c_114, c_128, c_112, c_4539])).
% 9.31/3.20  tff(c_4546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4045, c_166, c_4544])).
% 9.31/3.20  tff(c_4548, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_3878])).
% 9.31/3.20  tff(c_22, plain, (![A_18]: (k2_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.31/3.20  tff(c_134, plain, (![A_18]: (k2_relat_1(k6_partfun1(A_18))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_22])).
% 9.31/3.20  tff(c_4547, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_3878])).
% 9.31/3.20  tff(c_52, plain, (![A_28]: (k2_relat_1(k5_relat_1(A_28, k2_funct_1(A_28)))=k1_relat_1(A_28) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.31/3.20  tff(c_4643, plain, (k2_relat_1(k6_partfun1('#skF_3'))=k1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4547, c_52])).
% 9.31/3.20  tff(c_4660, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_292, c_118, c_4548, c_134, c_4643])).
% 9.31/3.20  tff(c_363, plain, (![A_104]: (k2_relat_1(k2_funct_1(A_104))=k1_relat_1(A_104) | ~v2_funct_1(A_104) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.31/3.20  tff(c_16, plain, (![A_10]: (k10_relat_1(A_10, k2_relat_1(A_10))=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.31/3.20  tff(c_7946, plain, (![A_365]: (k10_relat_1(k2_funct_1(A_365), k1_relat_1(A_365))=k1_relat_1(k2_funct_1(A_365)) | ~v1_relat_1(k2_funct_1(A_365)) | ~v2_funct_1(A_365) | ~v1_funct_1(A_365) | ~v1_relat_1(A_365))), inference(superposition, [status(thm), theory('equality')], [c_363, c_16])).
% 9.31/3.20  tff(c_7958, plain, (k10_relat_1(k2_funct_1('#skF_5'), '#skF_3')=k1_relat_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4660, c_7946])).
% 9.31/3.20  tff(c_7978, plain, (k10_relat_1(k2_funct_1('#skF_5'), '#skF_3')=k1_relat_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_118, c_4548, c_7958])).
% 9.31/3.20  tff(c_7989, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_7978])).
% 9.31/3.20  tff(c_7992, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_7989])).
% 9.31/3.20  tff(c_7996, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_292, c_118, c_7992])).
% 9.31/3.20  tff(c_7998, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_7978])).
% 9.31/3.20  tff(c_386, plain, (![A_105]: (k1_relat_1(k2_funct_1(A_105))=k2_relat_1(A_105) | ~v2_funct_1(A_105) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.31/3.20  tff(c_8339, plain, (![A_379]: (k5_relat_1(k6_partfun1(k2_relat_1(A_379)), k2_funct_1(A_379))=k2_funct_1(A_379) | ~v1_relat_1(k2_funct_1(A_379)) | ~v2_funct_1(A_379) | ~v1_funct_1(A_379) | ~v1_relat_1(A_379))), inference(superposition, [status(thm), theory('equality')], [c_386, c_133])).
% 9.31/3.20  tff(c_8373, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_5'))=k2_funct_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3726, c_8339])).
% 9.31/3.20  tff(c_8401, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_5'))=k2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_292, c_118, c_4548, c_7998, c_8373])).
% 9.31/3.20  tff(c_2773, plain, (![D_196, F_195, C_199, E_200, A_198, B_197]: (k1_partfun1(A_198, B_197, C_199, D_196, E_200, F_195)=k5_relat_1(E_200, F_195) | ~m1_subset_1(F_195, k1_zfmisc_1(k2_zfmisc_1(C_199, D_196))) | ~v1_funct_1(F_195) | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_197))) | ~v1_funct_1(E_200))), inference(cnfTransformation, [status(thm)], [f_200])).
% 9.31/3.20  tff(c_2781, plain, (![A_198, B_197, E_200]: (k1_partfun1(A_198, B_197, '#skF_3', '#skF_2', E_200, '#skF_5')=k5_relat_1(E_200, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_197))) | ~v1_funct_1(E_200))), inference(resolution, [status(thm)], [c_114, c_2773])).
% 9.31/3.20  tff(c_3776, plain, (![A_242, B_243, E_244]: (k1_partfun1(A_242, B_243, '#skF_3', '#skF_2', E_244, '#skF_5')=k5_relat_1(E_244, '#skF_5') | ~m1_subset_1(E_244, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))) | ~v1_funct_1(E_244))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_2781])).
% 9.31/3.20  tff(c_3791, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_120, c_3776])).
% 9.31/3.20  tff(c_3804, plain, (k5_relat_1('#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_2110, c_3791])).
% 9.31/3.20  tff(c_3817, plain, (![C_17]: (k5_relat_1(k6_partfun1('#skF_2'), C_17)=k5_relat_1('#skF_4', k5_relat_1('#skF_5', C_17)) | ~v1_relat_1(C_17) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3804, c_18])).
% 9.31/3.20  tff(c_3827, plain, (![C_17]: (k5_relat_1(k6_partfun1('#skF_2'), C_17)=k5_relat_1('#skF_4', k5_relat_1('#skF_5', C_17)) | ~v1_relat_1(C_17))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_292, c_3817])).
% 9.31/3.20  tff(c_8414, plain, (k5_relat_1('#skF_4', k5_relat_1('#skF_5', k2_funct_1('#skF_5')))=k2_funct_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8401, c_3827])).
% 9.31/3.20  tff(c_8438, plain, (k2_funct_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7998, c_441, c_4547, c_8414])).
% 9.31/3.20  tff(c_8456, plain, (k5_relat_1('#skF_5', '#skF_4')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8438, c_4547])).
% 9.31/3.20  tff(c_8628, plain, (![C_17]: (k5_relat_1(k6_partfun1('#skF_3'), C_17)=k5_relat_1('#skF_5', k5_relat_1('#skF_4', C_17)) | ~v1_relat_1(C_17) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8456, c_18])).
% 9.31/3.20  tff(c_9396, plain, (![C_398]: (k5_relat_1(k6_partfun1('#skF_3'), C_398)=k5_relat_1('#skF_5', k5_relat_1('#skF_4', C_398)) | ~v1_relat_1(C_398))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_295, c_8628])).
% 9.31/3.20  tff(c_8379, plain, (k5_relat_1(k6_partfun1('#skF_3'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_423, c_8339])).
% 9.31/3.20  tff(c_8403, plain, (k5_relat_1(k6_partfun1('#skF_3'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_295, c_124, c_108, c_2352, c_8379])).
% 9.31/3.20  tff(c_9406, plain, (k5_relat_1('#skF_5', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9396, c_8403])).
% 9.31/3.20  tff(c_9507, plain, (k2_funct_1('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2352, c_3770, c_3886, c_9406])).
% 9.31/3.20  tff(c_9509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_9507])).
% 9.31/3.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.31/3.20  
% 9.31/3.20  Inference rules
% 9.31/3.20  ----------------------
% 9.31/3.20  #Ref     : 0
% 9.31/3.20  #Sup     : 2033
% 9.31/3.20  #Fact    : 0
% 9.31/3.20  #Define  : 0
% 9.31/3.20  #Split   : 17
% 9.31/3.20  #Chain   : 0
% 9.31/3.20  #Close   : 0
% 9.31/3.20  
% 9.31/3.20  Ordering : KBO
% 9.31/3.20  
% 9.31/3.20  Simplification rules
% 9.31/3.20  ----------------------
% 9.31/3.20  #Subsume      : 55
% 9.31/3.20  #Demod        : 4268
% 9.31/3.20  #Tautology    : 1135
% 9.31/3.20  #SimpNegUnit  : 60
% 9.31/3.20  #BackRed      : 112
% 9.31/3.20  
% 9.31/3.20  #Partial instantiations: 0
% 9.31/3.20  #Strategies tried      : 1
% 9.31/3.20  
% 9.31/3.20  Timing (in seconds)
% 9.31/3.20  ----------------------
% 9.31/3.21  Preprocessing        : 0.40
% 9.31/3.21  Parsing              : 0.20
% 9.31/3.21  CNF conversion       : 0.03
% 9.31/3.21  Main loop            : 1.97
% 9.31/3.21  Inferencing          : 0.59
% 9.31/3.21  Reduction            : 0.88
% 9.31/3.21  Demodulation         : 0.70
% 9.31/3.21  BG Simplification    : 0.07
% 9.31/3.21  Subsumption          : 0.31
% 9.31/3.21  Abstraction          : 0.09
% 9.31/3.21  MUC search           : 0.00
% 9.31/3.21  Cooper               : 0.00
% 9.31/3.21  Total                : 2.42
% 9.31/3.21  Index Insertion      : 0.00
% 9.31/3.21  Index Deletion       : 0.00
% 9.31/3.21  Index Matching       : 0.00
% 9.31/3.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
