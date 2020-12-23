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
% DateTime   : Thu Dec  3 10:12:57 EST 2020

% Result     : Theorem 5.42s
% Output     : CNFRefutation 5.96s
% Verified   : 
% Statistics : Number of formulae       :  165 (1932 expanded)
%              Number of leaves         :   46 ( 694 expanded)
%              Depth                    :   28
%              Number of atoms          :  346 (5555 expanded)
%              Number of equality atoms :  115 (1639 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_175,negated_conjecture,(
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

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_121,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_133,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_45,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_149,axiom,(
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

tff(f_117,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_131,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_56,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_120,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_132,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_120])).

tff(c_193,plain,(
    ! [C_73,A_74,B_75] :
      ( v4_relat_1(C_73,A_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_205,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_193])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_131,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_120])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_18,plain,(
    ! [A_14] :
      ( v1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_62,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_410,plain,(
    ! [A_92,B_93,C_94] :
      ( k2_relset_1(A_92,B_93,C_94) = k2_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_416,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_410])).

tff(c_423,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_416])).

tff(c_22,plain,(
    ! [A_15] :
      ( k1_relat_1(k2_funct_1(A_15)) = k2_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_46,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_221,plain,(
    ! [A_77] : v4_relat_1(k6_partfun1(A_77),A_77) ),
    inference(resolution,[status(thm)],[c_46,c_193])).

tff(c_130,plain,(
    ! [A_36] : v1_relat_1(k6_partfun1(A_36)) ),
    inference(resolution,[status(thm)],[c_46,c_120])).

tff(c_50,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_8,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_84,plain,(
    ! [A_10] : k1_relat_1(k6_partfun1(A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8])).

tff(c_157,plain,(
    ! [B_61,A_62] :
      ( r1_tarski(k1_relat_1(B_61),A_62)
      | ~ v4_relat_1(B_61,A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_160,plain,(
    ! [A_10,A_62] :
      ( r1_tarski(A_10,A_62)
      | ~ v4_relat_1(k6_partfun1(A_10),A_62)
      | ~ v1_relat_1(k6_partfun1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_157])).

tff(c_162,plain,(
    ! [A_10,A_62] :
      ( r1_tarski(A_10,A_62)
      | ~ v4_relat_1(k6_partfun1(A_10),A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_160])).

tff(c_226,plain,(
    ! [A_78] : r1_tarski(A_78,A_78) ),
    inference(resolution,[status(thm)],[c_221,c_162])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( v4_relat_1(B_2,A_1)
      | ~ r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_244,plain,(
    ! [B_80] :
      ( v4_relat_1(B_80,k1_relat_1(B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_226,c_2])).

tff(c_481,plain,(
    ! [A_98] :
      ( v4_relat_1(k2_funct_1(A_98),k2_relat_1(A_98))
      | ~ v1_relat_1(k2_funct_1(A_98))
      | ~ v2_funct_1(A_98)
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_244])).

tff(c_484,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_481])).

tff(c_492,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_78,c_62,c_484])).

tff(c_495,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_492])).

tff(c_498,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_495])).

tff(c_502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_78,c_498])).

tff(c_504,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_492])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_10,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_83,plain,(
    ! [A_10] : k2_relat_1(k6_partfun1(A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_10])).

tff(c_14,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k6_relat_1(k2_relat_1(A_13))) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_134,plain,(
    ! [A_59] :
      ( k5_relat_1(A_59,k6_partfun1(k2_relat_1(A_59))) = A_59
      | ~ v1_relat_1(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_14])).

tff(c_143,plain,(
    ! [A_10] :
      ( k5_relat_1(k6_partfun1(A_10),k6_partfun1(A_10)) = k6_partfun1(A_10)
      | ~ v1_relat_1(k6_partfun1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_134])).

tff(c_147,plain,(
    ! [A_10] : k5_relat_1(k6_partfun1(A_10),k6_partfun1(A_10)) = k6_partfun1(A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_143])).

tff(c_26,plain,(
    ! [A_16] :
      ( k5_relat_1(A_16,k2_funct_1(A_16)) = k6_relat_1(k1_relat_1(A_16))
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_79,plain,(
    ! [A_16] :
      ( k5_relat_1(A_16,k2_funct_1(A_16)) = k6_partfun1(k1_relat_1(A_16))
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_26])).

tff(c_81,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k6_partfun1(k2_relat_1(A_13))) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_14])).

tff(c_428,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_81])).

tff(c_432,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_428])).

tff(c_225,plain,(
    ! [A_77] : r1_tarski(A_77,A_77) ),
    inference(resolution,[status(thm)],[c_221,c_162])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k5_relat_1(k6_relat_1(A_11),B_12) = B_12
      | ~ r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_260,plain,(
    ! [A_81,B_82] :
      ( k5_relat_1(k6_partfun1(A_81),B_82) = B_82
      | ~ r1_tarski(k1_relat_1(B_82),A_81)
      | ~ v1_relat_1(B_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_12])).

tff(c_274,plain,(
    ! [B_82] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(B_82)),B_82) = B_82
      | ~ v1_relat_1(B_82) ) ),
    inference(resolution,[status(thm)],[c_225,c_260])).

tff(c_506,plain,(
    ! [A_100,B_101,C_102] :
      ( k5_relat_1(k5_relat_1(A_100,B_101),C_102) = k5_relat_1(A_100,k5_relat_1(B_101,C_102))
      | ~ v1_relat_1(C_102)
      | ~ v1_relat_1(B_101)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_548,plain,(
    ! [B_82,C_102] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(B_82)),k5_relat_1(B_82,C_102)) = k5_relat_1(B_82,C_102)
      | ~ v1_relat_1(C_102)
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(B_82)))
      | ~ v1_relat_1(B_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_506])).

tff(c_817,plain,(
    ! [B_112,C_113] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(B_112)),k5_relat_1(B_112,C_113)) = k5_relat_1(B_112,C_113)
      | ~ v1_relat_1(C_113)
      | ~ v1_relat_1(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_548])).

tff(c_859,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),'#skF_3') = k5_relat_1('#skF_3',k6_partfun1('#skF_2'))
    | ~ v1_relat_1(k6_partfun1('#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_817])).

tff(c_900,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_130,c_432,c_859])).

tff(c_6,plain,(
    ! [A_3,B_7,C_9] :
      ( k5_relat_1(k5_relat_1(A_3,B_7),C_9) = k5_relat_1(A_3,k5_relat_1(B_7,C_9))
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_923,plain,(
    ! [C_9] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k5_relat_1('#skF_3',C_9)) = k5_relat_1('#skF_3',C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_900,c_6])).

tff(c_1937,plain,(
    ! [C_152] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k5_relat_1('#skF_3',C_152)) = k5_relat_1('#skF_3',C_152)
      | ~ v1_relat_1(C_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_131,c_923])).

tff(c_1973,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1(k1_relat_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_1937])).

tff(c_2001,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_78,c_62,c_504,c_147,c_1973])).

tff(c_2645,plain,(
    ! [A_183,C_184,B_185] :
      ( k6_partfun1(A_183) = k5_relat_1(C_184,k2_funct_1(C_184))
      | k1_xboole_0 = B_185
      | ~ v2_funct_1(C_184)
      | k2_relset_1(A_183,B_185,C_184) != B_185
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_183,B_185)))
      | ~ v1_funct_2(C_184,A_183,B_185)
      | ~ v1_funct_1(C_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2649,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_2645])).

tff(c_2657,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_66,c_62,c_2001,c_2649])).

tff(c_2658,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2657])).

tff(c_2742,plain,(
    k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2658,c_84])).

tff(c_2770,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2742])).

tff(c_2341,plain,(
    ! [A_175,C_176,B_177] :
      ( k6_partfun1(A_175) = k5_relat_1(C_176,k2_funct_1(C_176))
      | k1_xboole_0 = B_177
      | ~ v2_funct_1(C_176)
      | k2_relset_1(A_175,B_177,C_176) != B_177
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_175,B_177)))
      | ~ v1_funct_2(C_176,A_175,B_177)
      | ~ v1_funct_1(C_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2345,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_2341])).

tff(c_2353,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_66,c_62,c_2001,c_2345])).

tff(c_2354,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2353])).

tff(c_2438,plain,(
    k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2354,c_84])).

tff(c_2466,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2438])).

tff(c_20,plain,(
    ! [A_15] :
      ( k2_relat_1(k2_funct_1(A_15)) = k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_273,plain,(
    ! [A_81,A_10] :
      ( k5_relat_1(k6_partfun1(A_81),k6_partfun1(A_10)) = k6_partfun1(A_10)
      | ~ r1_tarski(A_10,A_81)
      | ~ v1_relat_1(k6_partfun1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_260])).

tff(c_277,plain,(
    ! [A_81,A_10] :
      ( k5_relat_1(k6_partfun1(A_81),k6_partfun1(A_10)) = k6_partfun1(A_10)
      | ~ r1_tarski(A_10,A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_273])).

tff(c_2016,plain,(
    ! [C_9] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),C_9) = k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),C_9))
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2001,c_6])).

tff(c_2038,plain,(
    ! [C_153] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),C_153) = k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),C_153))
      | ~ v1_relat_1(C_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_504,c_2016])).

tff(c_2128,plain,(
    ! [A_10] :
      ( k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(A_10))) = k6_partfun1(A_10)
      | ~ v1_relat_1(k6_partfun1(A_10))
      | ~ r1_tarski(A_10,k1_relat_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_2038])).

tff(c_2282,plain,(
    ! [A_170] :
      ( k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(A_170))) = k6_partfun1(A_170)
      | ~ r1_tarski(A_170,k1_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_2128])).

tff(c_2307,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_2282])).

tff(c_2321,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) = k6_partfun1(k1_relat_1('#skF_3'))
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_2001,c_2307])).

tff(c_2340,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2321])).

tff(c_2636,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2466,c_2340])).

tff(c_2639,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2636])).

tff(c_2642,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_78,c_62,c_225,c_2466,c_2639])).

tff(c_2643,plain,(
    k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) = k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2321])).

tff(c_2991,plain,(
    k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2770,c_2643])).

tff(c_3049,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2991,c_81])).

tff(c_3085,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_3049])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1821,plain,(
    ! [E_149,D_150,C_145,A_148,B_146,F_147] :
      ( m1_subset_1(k1_partfun1(A_148,B_146,C_145,D_150,E_149,F_147),k1_zfmisc_1(k2_zfmisc_1(A_148,D_150)))
      | ~ m1_subset_1(F_147,k1_zfmisc_1(k2_zfmisc_1(C_145,D_150)))
      | ~ v1_funct_1(F_147)
      | ~ m1_subset_1(E_149,k1_zfmisc_1(k2_zfmisc_1(A_148,B_146)))
      | ~ v1_funct_1(E_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_64,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_688,plain,(
    ! [D_106,C_107,A_108,B_109] :
      ( D_106 = C_107
      | ~ r2_relset_1(A_108,B_109,C_107,D_106)
      | ~ m1_subset_1(D_106,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_696,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_64,c_688])).

tff(c_711,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_696])).

tff(c_957,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_711])).

tff(c_1838,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1821,c_957])).

tff(c_1862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_1838])).

tff(c_1863,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_711])).

tff(c_2266,plain,(
    ! [A_163,D_166,B_164,E_167,F_165,C_168] :
      ( k1_partfun1(A_163,B_164,C_168,D_166,E_167,F_165) = k5_relat_1(E_167,F_165)
      | ~ m1_subset_1(F_165,k1_zfmisc_1(k2_zfmisc_1(C_168,D_166)))
      | ~ v1_funct_1(F_165)
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164)))
      | ~ v1_funct_1(E_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2272,plain,(
    ! [A_163,B_164,E_167] :
      ( k1_partfun1(A_163,B_164,'#skF_2','#skF_1',E_167,'#skF_4') = k5_relat_1(E_167,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164)))
      | ~ v1_funct_1(E_167) ) ),
    inference(resolution,[status(thm)],[c_68,c_2266])).

tff(c_3508,plain,(
    ! [A_204,B_205,E_206] :
      ( k1_partfun1(A_204,B_205,'#skF_2','#skF_1',E_206,'#skF_4') = k5_relat_1(E_206,'#skF_4')
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205)))
      | ~ v1_funct_1(E_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2272])).

tff(c_3517,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_3508])).

tff(c_3525,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1863,c_3517])).

tff(c_2850,plain,(
    ! [B_186,C_187,A_188] :
      ( k6_partfun1(B_186) = k5_relat_1(k2_funct_1(C_187),C_187)
      | k1_xboole_0 = B_186
      | ~ v2_funct_1(C_187)
      | k2_relset_1(A_188,B_186,C_187) != B_186
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_188,B_186)))
      | ~ v1_funct_2(C_187,A_188,B_186)
      | ~ v1_funct_1(C_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2854,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_2850])).

tff(c_2862,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_66,c_62,c_2854])).

tff(c_2863,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2862])).

tff(c_2879,plain,(
    ! [C_9] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_9)) = k5_relat_1(k6_partfun1('#skF_2'),C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2863,c_6])).

tff(c_4523,plain,(
    ! [C_223] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_223)) = k5_relat_1(k6_partfun1('#skF_2'),C_223)
      | ~ v1_relat_1(C_223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_131,c_2879])).

tff(c_4565,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3525,c_4523])).

tff(c_4606,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_3085,c_4565])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_275,plain,(
    ! [A_1,B_2] :
      ( k5_relat_1(k6_partfun1(A_1),B_2) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_260])).

tff(c_4635,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4606,c_275])).

tff(c_4652,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_205,c_4635])).

tff(c_4654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_4652])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:00:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.42/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.82/2.08  
% 5.82/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.82/2.08  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.82/2.08  
% 5.82/2.08  %Foreground sorts:
% 5.82/2.08  
% 5.82/2.08  
% 5.82/2.08  %Background operators:
% 5.82/2.08  
% 5.82/2.08  
% 5.82/2.08  %Foreground operators:
% 5.82/2.08  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.82/2.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.82/2.08  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.82/2.08  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.82/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.82/2.08  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.82/2.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.82/2.08  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.82/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.82/2.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.82/2.08  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.82/2.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.82/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.82/2.08  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.82/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.82/2.08  tff('#skF_1', type, '#skF_1': $i).
% 5.82/2.08  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.82/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.82/2.08  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.82/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.82/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.82/2.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.82/2.08  tff('#skF_4', type, '#skF_4': $i).
% 5.82/2.08  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.82/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.82/2.08  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.82/2.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.82/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.82/2.08  
% 5.96/2.11  tff(f_175, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 5.96/2.11  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.96/2.11  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.96/2.11  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.96/2.11  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.96/2.11  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 5.96/2.11  tff(f_121, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.96/2.11  tff(f_133, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.96/2.11  tff(f_45, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.96/2.11  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 5.96/2.11  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 5.96/2.11  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.96/2.11  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 5.96/2.11  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 5.96/2.11  tff(f_149, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 5.96/2.11  tff(f_117, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.96/2.11  tff(f_105, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.96/2.11  tff(f_131, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.96/2.11  tff(c_56, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.96/2.11  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.96/2.11  tff(c_120, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.96/2.11  tff(c_132, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_120])).
% 5.96/2.11  tff(c_193, plain, (![C_73, A_74, B_75]: (v4_relat_1(C_73, A_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.96/2.11  tff(c_205, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_193])).
% 5.96/2.11  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.96/2.11  tff(c_131, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_120])).
% 5.96/2.11  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.96/2.11  tff(c_18, plain, (![A_14]: (v1_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.96/2.11  tff(c_62, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.96/2.11  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.96/2.11  tff(c_410, plain, (![A_92, B_93, C_94]: (k2_relset_1(A_92, B_93, C_94)=k2_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.96/2.11  tff(c_416, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_410])).
% 5.96/2.11  tff(c_423, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_416])).
% 5.96/2.11  tff(c_22, plain, (![A_15]: (k1_relat_1(k2_funct_1(A_15))=k2_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.96/2.11  tff(c_46, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.96/2.11  tff(c_221, plain, (![A_77]: (v4_relat_1(k6_partfun1(A_77), A_77))), inference(resolution, [status(thm)], [c_46, c_193])).
% 5.96/2.11  tff(c_130, plain, (![A_36]: (v1_relat_1(k6_partfun1(A_36)))), inference(resolution, [status(thm)], [c_46, c_120])).
% 5.96/2.11  tff(c_50, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.96/2.11  tff(c_8, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.96/2.11  tff(c_84, plain, (![A_10]: (k1_relat_1(k6_partfun1(A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8])).
% 5.96/2.11  tff(c_157, plain, (![B_61, A_62]: (r1_tarski(k1_relat_1(B_61), A_62) | ~v4_relat_1(B_61, A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.96/2.11  tff(c_160, plain, (![A_10, A_62]: (r1_tarski(A_10, A_62) | ~v4_relat_1(k6_partfun1(A_10), A_62) | ~v1_relat_1(k6_partfun1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_157])).
% 5.96/2.11  tff(c_162, plain, (![A_10, A_62]: (r1_tarski(A_10, A_62) | ~v4_relat_1(k6_partfun1(A_10), A_62))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_160])).
% 5.96/2.11  tff(c_226, plain, (![A_78]: (r1_tarski(A_78, A_78))), inference(resolution, [status(thm)], [c_221, c_162])).
% 5.96/2.11  tff(c_2, plain, (![B_2, A_1]: (v4_relat_1(B_2, A_1) | ~r1_tarski(k1_relat_1(B_2), A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.96/2.11  tff(c_244, plain, (![B_80]: (v4_relat_1(B_80, k1_relat_1(B_80)) | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_226, c_2])).
% 5.96/2.11  tff(c_481, plain, (![A_98]: (v4_relat_1(k2_funct_1(A_98), k2_relat_1(A_98)) | ~v1_relat_1(k2_funct_1(A_98)) | ~v2_funct_1(A_98) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(superposition, [status(thm), theory('equality')], [c_22, c_244])).
% 5.96/2.11  tff(c_484, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_423, c_481])).
% 5.96/2.11  tff(c_492, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_78, c_62, c_484])).
% 5.96/2.11  tff(c_495, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_492])).
% 5.96/2.11  tff(c_498, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_495])).
% 5.96/2.11  tff(c_502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_78, c_498])).
% 5.96/2.11  tff(c_504, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_492])).
% 5.96/2.11  tff(c_58, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.96/2.11  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.96/2.11  tff(c_10, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.96/2.11  tff(c_83, plain, (![A_10]: (k2_relat_1(k6_partfun1(A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_10])).
% 5.96/2.11  tff(c_14, plain, (![A_13]: (k5_relat_1(A_13, k6_relat_1(k2_relat_1(A_13)))=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.96/2.11  tff(c_134, plain, (![A_59]: (k5_relat_1(A_59, k6_partfun1(k2_relat_1(A_59)))=A_59 | ~v1_relat_1(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_14])).
% 5.96/2.11  tff(c_143, plain, (![A_10]: (k5_relat_1(k6_partfun1(A_10), k6_partfun1(A_10))=k6_partfun1(A_10) | ~v1_relat_1(k6_partfun1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_83, c_134])).
% 5.96/2.11  tff(c_147, plain, (![A_10]: (k5_relat_1(k6_partfun1(A_10), k6_partfun1(A_10))=k6_partfun1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_143])).
% 5.96/2.11  tff(c_26, plain, (![A_16]: (k5_relat_1(A_16, k2_funct_1(A_16))=k6_relat_1(k1_relat_1(A_16)) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.96/2.11  tff(c_79, plain, (![A_16]: (k5_relat_1(A_16, k2_funct_1(A_16))=k6_partfun1(k1_relat_1(A_16)) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_26])).
% 5.96/2.11  tff(c_81, plain, (![A_13]: (k5_relat_1(A_13, k6_partfun1(k2_relat_1(A_13)))=A_13 | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_14])).
% 5.96/2.11  tff(c_428, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_423, c_81])).
% 5.96/2.11  tff(c_432, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_428])).
% 5.96/2.11  tff(c_225, plain, (![A_77]: (r1_tarski(A_77, A_77))), inference(resolution, [status(thm)], [c_221, c_162])).
% 5.96/2.11  tff(c_12, plain, (![A_11, B_12]: (k5_relat_1(k6_relat_1(A_11), B_12)=B_12 | ~r1_tarski(k1_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.96/2.11  tff(c_260, plain, (![A_81, B_82]: (k5_relat_1(k6_partfun1(A_81), B_82)=B_82 | ~r1_tarski(k1_relat_1(B_82), A_81) | ~v1_relat_1(B_82))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_12])).
% 5.96/2.11  tff(c_274, plain, (![B_82]: (k5_relat_1(k6_partfun1(k1_relat_1(B_82)), B_82)=B_82 | ~v1_relat_1(B_82))), inference(resolution, [status(thm)], [c_225, c_260])).
% 5.96/2.11  tff(c_506, plain, (![A_100, B_101, C_102]: (k5_relat_1(k5_relat_1(A_100, B_101), C_102)=k5_relat_1(A_100, k5_relat_1(B_101, C_102)) | ~v1_relat_1(C_102) | ~v1_relat_1(B_101) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.96/2.11  tff(c_548, plain, (![B_82, C_102]: (k5_relat_1(k6_partfun1(k1_relat_1(B_82)), k5_relat_1(B_82, C_102))=k5_relat_1(B_82, C_102) | ~v1_relat_1(C_102) | ~v1_relat_1(B_82) | ~v1_relat_1(k6_partfun1(k1_relat_1(B_82))) | ~v1_relat_1(B_82))), inference(superposition, [status(thm), theory('equality')], [c_274, c_506])).
% 5.96/2.11  tff(c_817, plain, (![B_112, C_113]: (k5_relat_1(k6_partfun1(k1_relat_1(B_112)), k5_relat_1(B_112, C_113))=k5_relat_1(B_112, C_113) | ~v1_relat_1(C_113) | ~v1_relat_1(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_548])).
% 5.96/2.11  tff(c_859, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), '#skF_3')=k5_relat_1('#skF_3', k6_partfun1('#skF_2')) | ~v1_relat_1(k6_partfun1('#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_432, c_817])).
% 5.96/2.11  tff(c_900, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_130, c_432, c_859])).
% 5.96/2.11  tff(c_6, plain, (![A_3, B_7, C_9]: (k5_relat_1(k5_relat_1(A_3, B_7), C_9)=k5_relat_1(A_3, k5_relat_1(B_7, C_9)) | ~v1_relat_1(C_9) | ~v1_relat_1(B_7) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.96/2.11  tff(c_923, plain, (![C_9]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k5_relat_1('#skF_3', C_9))=k5_relat_1('#skF_3', C_9) | ~v1_relat_1(C_9) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_900, c_6])).
% 5.96/2.11  tff(c_1937, plain, (![C_152]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k5_relat_1('#skF_3', C_152))=k5_relat_1('#skF_3', C_152) | ~v1_relat_1(C_152))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_131, c_923])).
% 5.96/2.11  tff(c_1973, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1(k1_relat_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_79, c_1937])).
% 5.96/2.11  tff(c_2001, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_78, c_62, c_504, c_147, c_1973])).
% 5.96/2.11  tff(c_2645, plain, (![A_183, C_184, B_185]: (k6_partfun1(A_183)=k5_relat_1(C_184, k2_funct_1(C_184)) | k1_xboole_0=B_185 | ~v2_funct_1(C_184) | k2_relset_1(A_183, B_185, C_184)!=B_185 | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_183, B_185))) | ~v1_funct_2(C_184, A_183, B_185) | ~v1_funct_1(C_184))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.96/2.11  tff(c_2649, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_2645])).
% 5.96/2.11  tff(c_2657, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_66, c_62, c_2001, c_2649])).
% 5.96/2.11  tff(c_2658, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_58, c_2657])).
% 5.96/2.11  tff(c_2742, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2658, c_84])).
% 5.96/2.11  tff(c_2770, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2742])).
% 5.96/2.11  tff(c_2341, plain, (![A_175, C_176, B_177]: (k6_partfun1(A_175)=k5_relat_1(C_176, k2_funct_1(C_176)) | k1_xboole_0=B_177 | ~v2_funct_1(C_176) | k2_relset_1(A_175, B_177, C_176)!=B_177 | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_175, B_177))) | ~v1_funct_2(C_176, A_175, B_177) | ~v1_funct_1(C_176))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.96/2.11  tff(c_2345, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_2341])).
% 5.96/2.11  tff(c_2353, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_66, c_62, c_2001, c_2345])).
% 5.96/2.11  tff(c_2354, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_58, c_2353])).
% 5.96/2.11  tff(c_2438, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2354, c_84])).
% 5.96/2.11  tff(c_2466, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2438])).
% 5.96/2.11  tff(c_20, plain, (![A_15]: (k2_relat_1(k2_funct_1(A_15))=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.96/2.11  tff(c_273, plain, (![A_81, A_10]: (k5_relat_1(k6_partfun1(A_81), k6_partfun1(A_10))=k6_partfun1(A_10) | ~r1_tarski(A_10, A_81) | ~v1_relat_1(k6_partfun1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_260])).
% 5.96/2.11  tff(c_277, plain, (![A_81, A_10]: (k5_relat_1(k6_partfun1(A_81), k6_partfun1(A_10))=k6_partfun1(A_10) | ~r1_tarski(A_10, A_81))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_273])).
% 5.96/2.11  tff(c_2016, plain, (![C_9]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), C_9)=k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), C_9)) | ~v1_relat_1(C_9) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2001, c_6])).
% 5.96/2.11  tff(c_2038, plain, (![C_153]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), C_153)=k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), C_153)) | ~v1_relat_1(C_153))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_504, c_2016])).
% 5.96/2.11  tff(c_2128, plain, (![A_10]: (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(A_10)))=k6_partfun1(A_10) | ~v1_relat_1(k6_partfun1(A_10)) | ~r1_tarski(A_10, k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_277, c_2038])).
% 5.96/2.11  tff(c_2282, plain, (![A_170]: (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(A_170)))=k6_partfun1(A_170) | ~r1_tarski(A_170, k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_2128])).
% 5.96/2.11  tff(c_2307, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_2282])).
% 5.96/2.11  tff(c_2321, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))=k6_partfun1(k1_relat_1('#skF_3')) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_504, c_2001, c_2307])).
% 5.96/2.11  tff(c_2340, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2321])).
% 5.96/2.11  tff(c_2636, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2466, c_2340])).
% 5.96/2.11  tff(c_2639, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_2636])).
% 5.96/2.11  tff(c_2642, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_78, c_62, c_225, c_2466, c_2639])).
% 5.96/2.11  tff(c_2643, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))=k6_partfun1(k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2321])).
% 5.96/2.11  tff(c_2991, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2770, c_2643])).
% 5.96/2.11  tff(c_3049, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2991, c_81])).
% 5.96/2.11  tff(c_3085, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_504, c_3049])).
% 5.96/2.11  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.96/2.11  tff(c_1821, plain, (![E_149, D_150, C_145, A_148, B_146, F_147]: (m1_subset_1(k1_partfun1(A_148, B_146, C_145, D_150, E_149, F_147), k1_zfmisc_1(k2_zfmisc_1(A_148, D_150))) | ~m1_subset_1(F_147, k1_zfmisc_1(k2_zfmisc_1(C_145, D_150))) | ~v1_funct_1(F_147) | ~m1_subset_1(E_149, k1_zfmisc_1(k2_zfmisc_1(A_148, B_146))) | ~v1_funct_1(E_149))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.96/2.11  tff(c_64, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.96/2.11  tff(c_688, plain, (![D_106, C_107, A_108, B_109]: (D_106=C_107 | ~r2_relset_1(A_108, B_109, C_107, D_106) | ~m1_subset_1(D_106, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.96/2.11  tff(c_696, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_64, c_688])).
% 5.96/2.11  tff(c_711, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_696])).
% 5.96/2.11  tff(c_957, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_711])).
% 5.96/2.11  tff(c_1838, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1821, c_957])).
% 5.96/2.11  tff(c_1862, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_1838])).
% 5.96/2.11  tff(c_1863, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_711])).
% 5.96/2.11  tff(c_2266, plain, (![A_163, D_166, B_164, E_167, F_165, C_168]: (k1_partfun1(A_163, B_164, C_168, D_166, E_167, F_165)=k5_relat_1(E_167, F_165) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(C_168, D_166))) | ~v1_funct_1(F_165) | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))) | ~v1_funct_1(E_167))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.96/2.11  tff(c_2272, plain, (![A_163, B_164, E_167]: (k1_partfun1(A_163, B_164, '#skF_2', '#skF_1', E_167, '#skF_4')=k5_relat_1(E_167, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))) | ~v1_funct_1(E_167))), inference(resolution, [status(thm)], [c_68, c_2266])).
% 5.96/2.11  tff(c_3508, plain, (![A_204, B_205, E_206]: (k1_partfun1(A_204, B_205, '#skF_2', '#skF_1', E_206, '#skF_4')=k5_relat_1(E_206, '#skF_4') | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))) | ~v1_funct_1(E_206))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2272])).
% 5.96/2.11  tff(c_3517, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_3508])).
% 5.96/2.11  tff(c_3525, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1863, c_3517])).
% 5.96/2.11  tff(c_2850, plain, (![B_186, C_187, A_188]: (k6_partfun1(B_186)=k5_relat_1(k2_funct_1(C_187), C_187) | k1_xboole_0=B_186 | ~v2_funct_1(C_187) | k2_relset_1(A_188, B_186, C_187)!=B_186 | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_188, B_186))) | ~v1_funct_2(C_187, A_188, B_186) | ~v1_funct_1(C_187))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.96/2.11  tff(c_2854, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_2850])).
% 5.96/2.11  tff(c_2862, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_66, c_62, c_2854])).
% 5.96/2.11  tff(c_2863, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_58, c_2862])).
% 5.96/2.11  tff(c_2879, plain, (![C_9]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_9))=k5_relat_1(k6_partfun1('#skF_2'), C_9) | ~v1_relat_1(C_9) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2863, c_6])).
% 5.96/2.11  tff(c_4523, plain, (![C_223]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_223))=k5_relat_1(k6_partfun1('#skF_2'), C_223) | ~v1_relat_1(C_223))), inference(demodulation, [status(thm), theory('equality')], [c_504, c_131, c_2879])).
% 5.96/2.11  tff(c_4565, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3525, c_4523])).
% 5.96/2.11  tff(c_4606, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_3085, c_4565])).
% 5.96/2.11  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.96/2.11  tff(c_275, plain, (![A_1, B_2]: (k5_relat_1(k6_partfun1(A_1), B_2)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_260])).
% 5.96/2.11  tff(c_4635, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4606, c_275])).
% 5.96/2.11  tff(c_4652, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_205, c_4635])).
% 5.96/2.11  tff(c_4654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_4652])).
% 5.96/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.96/2.11  
% 5.96/2.11  Inference rules
% 5.96/2.11  ----------------------
% 5.96/2.11  #Ref     : 0
% 5.96/2.11  #Sup     : 968
% 5.96/2.11  #Fact    : 0
% 5.96/2.11  #Define  : 0
% 5.96/2.11  #Split   : 10
% 5.96/2.11  #Chain   : 0
% 5.96/2.11  #Close   : 0
% 5.96/2.11  
% 5.96/2.11  Ordering : KBO
% 5.96/2.11  
% 5.96/2.11  Simplification rules
% 5.96/2.11  ----------------------
% 5.96/2.11  #Subsume      : 41
% 5.96/2.11  #Demod        : 1545
% 5.96/2.11  #Tautology    : 505
% 5.96/2.11  #SimpNegUnit  : 19
% 5.96/2.11  #BackRed      : 28
% 5.96/2.11  
% 5.96/2.11  #Partial instantiations: 0
% 5.96/2.11  #Strategies tried      : 1
% 5.96/2.11  
% 5.96/2.11  Timing (in seconds)
% 5.96/2.11  ----------------------
% 5.96/2.11  Preprocessing        : 0.36
% 5.96/2.11  Parsing              : 0.19
% 5.96/2.11  CNF conversion       : 0.02
% 5.96/2.11  Main loop            : 0.96
% 5.96/2.11  Inferencing          : 0.32
% 5.96/2.11  Reduction            : 0.37
% 5.96/2.11  Demodulation         : 0.28
% 5.98/2.11  BG Simplification    : 0.04
% 5.98/2.11  Subsumption          : 0.17
% 5.98/2.11  Abstraction          : 0.05
% 5.98/2.11  MUC search           : 0.00
% 5.98/2.11  Cooper               : 0.00
% 5.98/2.11  Total                : 1.37
% 5.98/2.11  Index Insertion      : 0.00
% 5.98/2.11  Index Deletion       : 0.00
% 5.98/2.11  Index Matching       : 0.00
% 5.98/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
