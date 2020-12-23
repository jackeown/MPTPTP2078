%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:56 EST 2020

% Result     : Theorem 9.65s
% Output     : CNFRefutation 9.78s
% Verified   : 
% Statistics : Number of formulae       :  194 (3210 expanded)
%              Number of leaves         :   48 (1128 expanded)
%              Depth                    :   34
%              Number of atoms          :  398 (8335 expanded)
%              Number of equality atoms :  107 (2496 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_174,negated_conjecture,(
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

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_148,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_124,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_136,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_122,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_146,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_60,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_138,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_150,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_138])).

tff(c_270,plain,(
    ! [C_85,A_86,B_87] :
      ( v4_relat_1(C_85,A_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_283,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_270])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( k7_relat_1(B_6,A_5) = B_6
      | ~ v4_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_292,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_283,c_12])).

tff(c_295,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_292])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_149,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_138])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_28,plain,(
    ! [A_21] :
      ( v1_relat_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_66,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_282,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_270])).

tff(c_286,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_282,c_12])).

tff(c_289,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_286])).

tff(c_58,plain,(
    ! [A_50] : k6_relat_1(A_50) = k6_partfun1(A_50) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_50,plain,(
    ! [A_37] : m1_subset_1(k6_relat_1(A_37),k1_zfmisc_1(k2_zfmisc_1(A_37,A_37))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_83,plain,(
    ! [A_37] : m1_subset_1(k6_partfun1(A_37),k1_zfmisc_1(k2_zfmisc_1(A_37,A_37))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50])).

tff(c_148,plain,(
    ! [A_37] : v1_relat_1(k6_partfun1(A_37)) ),
    inference(resolution,[status(thm)],[c_83,c_138])).

tff(c_18,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_89,plain,(
    ! [A_17] : k1_relat_1(k6_partfun1(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_18])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( k5_relat_1(k6_relat_1(A_19),B_20) = k7_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_86,plain,(
    ! [A_19,B_20] :
      ( k5_relat_1(k6_partfun1(A_19),B_20) = k7_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_24])).

tff(c_420,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_98,B_99)),k1_relat_1(A_98))
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_434,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_20,A_19)),k1_relat_1(k6_partfun1(A_19)))
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(k6_partfun1(A_19))
      | ~ v1_relat_1(B_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_420])).

tff(c_451,plain,(
    ! [B_100,A_101] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_100,A_101)),A_101)
      | ~ v1_relat_1(B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_89,c_434])).

tff(c_468,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_451])).

tff(c_480,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_468])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_524,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_480,c_2])).

tff(c_547,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_524])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1537,plain,(
    ! [C_165,D_166,E_163,A_161,B_162,F_164] :
      ( m1_subset_1(k1_partfun1(A_161,B_162,C_165,D_166,E_163,F_164),k1_zfmisc_1(k2_zfmisc_1(A_161,D_166)))
      | ~ m1_subset_1(F_164,k1_zfmisc_1(k2_zfmisc_1(C_165,D_166)))
      | ~ v1_funct_1(F_164)
      | ~ m1_subset_1(E_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162)))
      | ~ v1_funct_1(E_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_68,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_839,plain,(
    ! [D_121,C_122,A_123,B_124] :
      ( D_121 = C_122
      | ~ r2_relset_1(A_123,B_124,C_122,D_121)
      | ~ m1_subset_1(D_121,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124)))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_847,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_839])).

tff(c_862,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_847])).

tff(c_1021,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_862])).

tff(c_1550,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1537,c_1021])).

tff(c_1572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_1550])).

tff(c_1573,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_862])).

tff(c_2094,plain,(
    ! [F_190,A_194,E_189,B_193,D_191,C_192] :
      ( k1_partfun1(A_194,B_193,C_192,D_191,E_189,F_190) = k5_relat_1(E_189,F_190)
      | ~ m1_subset_1(F_190,k1_zfmisc_1(k2_zfmisc_1(C_192,D_191)))
      | ~ v1_funct_1(F_190)
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(A_194,B_193)))
      | ~ v1_funct_1(E_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2100,plain,(
    ! [A_194,B_193,E_189] :
      ( k1_partfun1(A_194,B_193,'#skF_2','#skF_1',E_189,'#skF_4') = k5_relat_1(E_189,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(A_194,B_193)))
      | ~ v1_funct_1(E_189) ) ),
    inference(resolution,[status(thm)],[c_72,c_2094])).

tff(c_2275,plain,(
    ! [A_206,B_207,E_208] :
      ( k1_partfun1(A_206,B_207,'#skF_2','#skF_1',E_208,'#skF_4') = k5_relat_1(E_208,'#skF_4')
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207)))
      | ~ v1_funct_1(E_208) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2100])).

tff(c_2284,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_2275])).

tff(c_2292,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1573,c_2284])).

tff(c_70,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_483,plain,(
    ! [A_102,B_103,C_104] :
      ( k2_relset_1(A_102,B_103,C_104) = k2_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_489,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_483])).

tff(c_496,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_489])).

tff(c_22,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k6_relat_1(k2_relat_1(A_18))) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_87,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k6_partfun1(k2_relat_1(A_18))) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_22])).

tff(c_501,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_87])).

tff(c_505,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_501])).

tff(c_612,plain,(
    ! [A_111,B_112,C_113] :
      ( k5_relat_1(k5_relat_1(A_111,B_112),C_113) = k5_relat_1(A_111,k5_relat_1(B_112,C_113))
      | ~ v1_relat_1(C_113)
      | ~ v1_relat_1(B_112)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_637,plain,(
    ! [C_113] :
      ( k5_relat_1('#skF_3',k5_relat_1(k6_partfun1('#skF_2'),C_113)) = k5_relat_1('#skF_3',C_113)
      | ~ v1_relat_1(C_113)
      | ~ v1_relat_1(k6_partfun1('#skF_2'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_612])).

tff(c_665,plain,(
    ! [C_114] :
      ( k5_relat_1('#skF_3',k5_relat_1(k6_partfun1('#skF_2'),C_114)) = k5_relat_1('#skF_3',C_114)
      | ~ v1_relat_1(C_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_148,c_637])).

tff(c_753,plain,(
    ! [B_119] :
      ( k5_relat_1('#skF_3',k7_relat_1(B_119,'#skF_2')) = k5_relat_1('#skF_3',B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_relat_1(B_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_665])).

tff(c_14,plain,(
    ! [A_7,B_9] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_7,B_9)),k1_relat_1(A_7))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_762,plain,(
    ! [B_119] :
      ( r1_tarski(k1_relat_1(k5_relat_1('#skF_3',B_119)),k1_relat_1('#skF_3'))
      | ~ v1_relat_1(k7_relat_1(B_119,'#skF_2'))
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(B_119)
      | ~ v1_relat_1(B_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_14])).

tff(c_781,plain,(
    ! [B_119] :
      ( r1_tarski(k1_relat_1(k5_relat_1('#skF_3',B_119)),k1_relat_1('#skF_3'))
      | ~ v1_relat_1(k7_relat_1(B_119,'#skF_2'))
      | ~ v1_relat_1(B_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_762])).

tff(c_2302,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1('#skF_1')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2292,c_781])).

tff(c_2317,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_150,c_295,c_89,c_2302])).

tff(c_2319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_547,c_2317])).

tff(c_2320,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_524])).

tff(c_36,plain,(
    ! [A_23] :
      ( k5_relat_1(A_23,k2_funct_1(A_23)) = k6_relat_1(k1_relat_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_84,plain,(
    ! [A_23] :
      ( k5_relat_1(A_23,k2_funct_1(A_23)) = k6_partfun1(k1_relat_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_36])).

tff(c_2327,plain,(
    ! [B_9] :
      ( r1_tarski(k1_relat_1(k5_relat_1('#skF_3',B_9)),'#skF_1')
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2320,c_14])).

tff(c_2399,plain,(
    ! [B_213] :
      ( r1_tarski(k1_relat_1(k5_relat_1('#skF_3',B_213)),'#skF_1')
      | ~ v1_relat_1(B_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_2327])).

tff(c_2660,plain,(
    ! [B_229] :
      ( k1_relat_1(k5_relat_1('#skF_3',B_229)) = '#skF_1'
      | ~ r1_tarski('#skF_1',k1_relat_1(k5_relat_1('#skF_3',B_229)))
      | ~ v1_relat_1(B_229) ) ),
    inference(resolution,[status(thm)],[c_2399,c_2])).

tff(c_2664,plain,
    ( k1_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3'))) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_2660])).

tff(c_2673,plain,
    ( k1_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3'))) = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_82,c_66,c_6,c_2320,c_89,c_2664])).

tff(c_2743,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2673])).

tff(c_2746,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_2743])).

tff(c_2750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_82,c_2746])).

tff(c_2752,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2673])).

tff(c_30,plain,(
    ! [A_22] :
      ( k2_relat_1(k2_funct_1(A_22)) = k1_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_215,plain,(
    ! [B_79,A_80] :
      ( v4_relat_1(B_79,A_80)
      | ~ r1_tarski(k1_relat_1(B_79),A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_221,plain,(
    ! [A_17,A_80] :
      ( v4_relat_1(k6_partfun1(A_17),A_80)
      | ~ r1_tarski(A_17,A_80)
      | ~ v1_relat_1(k6_partfun1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_215])).

tff(c_259,plain,(
    ! [A_83,A_84] :
      ( v4_relat_1(k6_partfun1(A_83),A_84)
      | ~ r1_tarski(A_83,A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_221])).

tff(c_265,plain,(
    ! [A_83,A_84] :
      ( k7_relat_1(k6_partfun1(A_83),A_84) = k6_partfun1(A_83)
      | ~ v1_relat_1(k6_partfun1(A_83))
      | ~ r1_tarski(A_83,A_84) ) ),
    inference(resolution,[status(thm)],[c_259,c_12])).

tff(c_269,plain,(
    ! [A_83,A_84] :
      ( k7_relat_1(k6_partfun1(A_83),A_84) = k6_partfun1(A_83)
      | ~ r1_tarski(A_83,A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_265])).

tff(c_20,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_88,plain,(
    ! [A_17] : k2_relat_1(k6_partfun1(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_20])).

tff(c_159,plain,(
    ! [A_66,B_67] :
      ( k5_relat_1(k6_partfun1(A_66),B_67) = k7_relat_1(B_67,A_66)
      | ~ v1_relat_1(B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_24])).

tff(c_166,plain,(
    ! [A_66] :
      ( k7_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(A_66))),A_66) = k6_partfun1(A_66)
      | ~ v1_relat_1(k6_partfun1(A_66))
      | ~ v1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(A_66)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_87])).

tff(c_176,plain,(
    ! [A_66] : k7_relat_1(k6_partfun1(A_66),A_66) = k6_partfun1(A_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_88,c_148,c_88,c_166])).

tff(c_2751,plain,(
    k1_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3'))) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2673])).

tff(c_229,plain,(
    ! [B_79] :
      ( v4_relat_1(B_79,k1_relat_1(B_79))
      | ~ v1_relat_1(B_79) ) ),
    inference(resolution,[status(thm)],[c_6,c_215])).

tff(c_2777,plain,
    ( v4_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2751,c_229])).

tff(c_2914,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2777])).

tff(c_2917,plain,
    ( ~ v1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_2914])).

tff(c_2920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_82,c_66,c_148,c_2320,c_2917])).

tff(c_2922,plain,(
    v1_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2777])).

tff(c_2921,plain,(
    v4_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_2777])).

tff(c_2977,plain,
    ( k7_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3')),'#skF_1') = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2921,c_12])).

tff(c_2983,plain,(
    k7_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3')),'#skF_1') = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2922,c_2977])).

tff(c_2999,plain,
    ( k7_relat_1(k6_partfun1(k1_relat_1('#skF_3')),'#skF_1') = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_2983])).

tff(c_3009,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_82,c_66,c_176,c_2320,c_2999])).

tff(c_16,plain,(
    ! [A_10,B_14,C_16] :
      ( k5_relat_1(k5_relat_1(A_10,B_14),C_16) = k5_relat_1(A_10,k5_relat_1(B_14,C_16))
      | ~ v1_relat_1(C_16)
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3021,plain,(
    ! [C_16] :
      ( k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),C_16)) = k5_relat_1(k6_partfun1('#skF_1'),C_16)
      | ~ v1_relat_1(C_16)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3009,c_16])).

tff(c_3148,plain,(
    ! [C_242] :
      ( k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),C_242)) = k5_relat_1(k6_partfun1('#skF_1'),C_242)
      | ~ v1_relat_1(C_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_2752,c_3021])).

tff(c_3181,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_3148])).

tff(c_3193,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2752,c_148,c_3009,c_3181])).

tff(c_3243,plain,
    ( k7_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))),'#skF_1') = k6_partfun1('#skF_1')
    | ~ v1_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3193,c_86])).

tff(c_3261,plain,(
    k7_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))),'#skF_1') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_3243])).

tff(c_3729,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) = k6_partfun1('#skF_1')
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_3261])).

tff(c_3811,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3729])).

tff(c_3814,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3811])).

tff(c_3817,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_82,c_66,c_6,c_2320,c_3814])).

tff(c_3818,plain,(
    k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3729])).

tff(c_3885,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3818,c_87])).

tff(c_3909,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2752,c_3885])).

tff(c_3545,plain,(
    ! [A_258,F_254,C_256,E_253,D_255,B_257] :
      ( k1_partfun1(A_258,B_257,C_256,D_255,E_253,F_254) = k5_relat_1(E_253,F_254)
      | ~ m1_subset_1(F_254,k1_zfmisc_1(k2_zfmisc_1(C_256,D_255)))
      | ~ v1_funct_1(F_254)
      | ~ m1_subset_1(E_253,k1_zfmisc_1(k2_zfmisc_1(A_258,B_257)))
      | ~ v1_funct_1(E_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_3551,plain,(
    ! [A_258,B_257,E_253] :
      ( k1_partfun1(A_258,B_257,'#skF_2','#skF_1',E_253,'#skF_4') = k5_relat_1(E_253,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_253,k1_zfmisc_1(k2_zfmisc_1(A_258,B_257)))
      | ~ v1_funct_1(E_253) ) ),
    inference(resolution,[status(thm)],[c_72,c_3545])).

tff(c_3619,plain,(
    ! [A_268,B_269,E_270] :
      ( k1_partfun1(A_268,B_269,'#skF_2','#skF_1',E_270,'#skF_4') = k5_relat_1(E_270,'#skF_4')
      | ~ m1_subset_1(E_270,k1_zfmisc_1(k2_zfmisc_1(A_268,B_269)))
      | ~ v1_funct_1(E_270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3551])).

tff(c_3628,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_3619])).

tff(c_3636,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3628])).

tff(c_52,plain,(
    ! [D_41,B_39,A_38,F_43,E_42,C_40] :
      ( m1_subset_1(k1_partfun1(A_38,B_39,C_40,D_41,E_42,F_43),k1_zfmisc_1(k2_zfmisc_1(A_38,D_41)))
      | ~ m1_subset_1(F_43,k1_zfmisc_1(k2_zfmisc_1(C_40,D_41)))
      | ~ v1_funct_1(F_43)
      | ~ m1_subset_1(E_42,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_1(E_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3645,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3636,c_52])).

tff(c_3649,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_3645])).

tff(c_3124,plain,(
    ! [D_238,C_239,A_240,B_241] :
      ( D_238 = C_239
      | ~ r2_relset_1(A_240,B_241,C_239,D_238)
      | ~ m1_subset_1(D_238,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241)))
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_3132,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_3124])).

tff(c_3147,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_3132])).

tff(c_3267,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3147])).

tff(c_3704,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3649,c_3636,c_3267])).

tff(c_3705,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3147])).

tff(c_3991,plain,(
    ! [F_282,C_284,B_285,E_281,D_283,A_286] :
      ( k1_partfun1(A_286,B_285,C_284,D_283,E_281,F_282) = k5_relat_1(E_281,F_282)
      | ~ m1_subset_1(F_282,k1_zfmisc_1(k2_zfmisc_1(C_284,D_283)))
      | ~ v1_funct_1(F_282)
      | ~ m1_subset_1(E_281,k1_zfmisc_1(k2_zfmisc_1(A_286,B_285)))
      | ~ v1_funct_1(E_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_3997,plain,(
    ! [A_286,B_285,E_281] :
      ( k1_partfun1(A_286,B_285,'#skF_2','#skF_1',E_281,'#skF_4') = k5_relat_1(E_281,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_281,k1_zfmisc_1(k2_zfmisc_1(A_286,B_285)))
      | ~ v1_funct_1(E_281) ) ),
    inference(resolution,[status(thm)],[c_72,c_3991])).

tff(c_4516,plain,(
    ! [A_303,B_304,E_305] :
      ( k1_partfun1(A_303,B_304,'#skF_2','#skF_1',E_305,'#skF_4') = k5_relat_1(E_305,'#skF_4')
      | ~ m1_subset_1(E_305,k1_zfmisc_1(k2_zfmisc_1(A_303,B_304)))
      | ~ v1_funct_1(E_305) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3997])).

tff(c_4531,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_4516])).

tff(c_4545,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3705,c_4531])).

tff(c_34,plain,(
    ! [A_23] :
      ( k5_relat_1(k2_funct_1(A_23),A_23) = k6_relat_1(k2_relat_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_85,plain,(
    ! [A_23] :
      ( k5_relat_1(k2_funct_1(A_23),A_23) = k6_partfun1(k2_relat_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_34])).

tff(c_2800,plain,(
    ! [A_231,B_232,C_233] :
      ( k5_relat_1(k5_relat_1(A_231,B_232),C_233) = k5_relat_1(A_231,k5_relat_1(B_232,C_233))
      | ~ v1_relat_1(C_233)
      | ~ v1_relat_1(B_232)
      | ~ v1_relat_1(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8801,plain,(
    ! [A_382,C_383] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_382)),C_383) = k5_relat_1(k2_funct_1(A_382),k5_relat_1(A_382,C_383))
      | ~ v1_relat_1(C_383)
      | ~ v1_relat_1(A_382)
      | ~ v1_relat_1(k2_funct_1(A_382))
      | ~ v2_funct_1(A_382)
      | ~ v1_funct_1(A_382)
      | ~ v1_relat_1(A_382) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_2800])).

tff(c_9024,plain,(
    ! [C_383] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_383)) = k5_relat_1(k6_partfun1('#skF_2'),C_383)
      | ~ v1_relat_1(C_383)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_8801])).

tff(c_13327,plain,(
    ! [C_492] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_492)) = k5_relat_1(k6_partfun1('#skF_2'),C_492)
      | ~ v1_relat_1(C_492) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_82,c_66,c_2752,c_149,c_9024])).

tff(c_13441,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4545,c_13327])).

tff(c_13520,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_3909,c_13441])).

tff(c_13792,plain,
    ( k7_relat_1('#skF_4','#skF_2') = k2_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13520,c_86])).

tff(c_13833,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_295,c_13792])).

tff(c_13835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_13833])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n011.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 10:38:42 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.65/3.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.78/3.73  
% 9.78/3.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.78/3.74  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.78/3.74  
% 9.78/3.74  %Foreground sorts:
% 9.78/3.74  
% 9.78/3.74  
% 9.78/3.74  %Background operators:
% 9.78/3.74  
% 9.78/3.74  
% 9.78/3.74  %Foreground operators:
% 9.78/3.74  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.78/3.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.78/3.74  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.78/3.74  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.78/3.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.78/3.74  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.78/3.74  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.78/3.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.78/3.74  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.78/3.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.78/3.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.78/3.74  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.78/3.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.78/3.74  tff('#skF_2', type, '#skF_2': $i).
% 9.78/3.74  tff('#skF_3', type, '#skF_3': $i).
% 9.78/3.74  tff('#skF_1', type, '#skF_1': $i).
% 9.78/3.74  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.78/3.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.78/3.74  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.78/3.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.78/3.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.78/3.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.78/3.74  tff('#skF_4', type, '#skF_4': $i).
% 9.78/3.74  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.78/3.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.78/3.74  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.78/3.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.78/3.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.78/3.74  
% 9.78/3.76  tff(f_174, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 9.78/3.76  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.78/3.76  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.78/3.76  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 9.78/3.76  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.78/3.76  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.78/3.76  tff(f_148, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.78/3.76  tff(f_124, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 9.78/3.76  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 9.78/3.76  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 9.78/3.76  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 9.78/3.76  tff(f_136, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.78/3.76  tff(f_122, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.78/3.76  tff(f_146, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.78/3.76  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.78/3.76  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 9.78/3.76  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 9.78/3.76  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 9.78/3.76  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 9.78/3.76  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 9.78/3.76  tff(c_60, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.78/3.76  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.78/3.76  tff(c_138, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.78/3.76  tff(c_150, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_138])).
% 9.78/3.76  tff(c_270, plain, (![C_85, A_86, B_87]: (v4_relat_1(C_85, A_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.78/3.76  tff(c_283, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_270])).
% 9.78/3.76  tff(c_12, plain, (![B_6, A_5]: (k7_relat_1(B_6, A_5)=B_6 | ~v4_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.78/3.76  tff(c_292, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_283, c_12])).
% 9.78/3.76  tff(c_295, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_292])).
% 9.78/3.76  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.78/3.76  tff(c_149, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_138])).
% 9.78/3.76  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.78/3.76  tff(c_28, plain, (![A_21]: (v1_relat_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.78/3.76  tff(c_66, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.78/3.76  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.78/3.76  tff(c_282, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_270])).
% 9.78/3.76  tff(c_286, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_282, c_12])).
% 9.78/3.76  tff(c_289, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_286])).
% 9.78/3.76  tff(c_58, plain, (![A_50]: (k6_relat_1(A_50)=k6_partfun1(A_50))), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.78/3.76  tff(c_50, plain, (![A_37]: (m1_subset_1(k6_relat_1(A_37), k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.78/3.76  tff(c_83, plain, (![A_37]: (m1_subset_1(k6_partfun1(A_37), k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50])).
% 9.78/3.76  tff(c_148, plain, (![A_37]: (v1_relat_1(k6_partfun1(A_37)))), inference(resolution, [status(thm)], [c_83, c_138])).
% 9.78/3.76  tff(c_18, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.78/3.76  tff(c_89, plain, (![A_17]: (k1_relat_1(k6_partfun1(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_18])).
% 9.78/3.76  tff(c_24, plain, (![A_19, B_20]: (k5_relat_1(k6_relat_1(A_19), B_20)=k7_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.78/3.76  tff(c_86, plain, (![A_19, B_20]: (k5_relat_1(k6_partfun1(A_19), B_20)=k7_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_24])).
% 9.78/3.76  tff(c_420, plain, (![A_98, B_99]: (r1_tarski(k1_relat_1(k5_relat_1(A_98, B_99)), k1_relat_1(A_98)) | ~v1_relat_1(B_99) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.78/3.76  tff(c_434, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(k7_relat_1(B_20, A_19)), k1_relat_1(k6_partfun1(A_19))) | ~v1_relat_1(B_20) | ~v1_relat_1(k6_partfun1(A_19)) | ~v1_relat_1(B_20))), inference(superposition, [status(thm), theory('equality')], [c_86, c_420])).
% 9.78/3.76  tff(c_451, plain, (![B_100, A_101]: (r1_tarski(k1_relat_1(k7_relat_1(B_100, A_101)), A_101) | ~v1_relat_1(B_100))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_89, c_434])).
% 9.78/3.76  tff(c_468, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_289, c_451])).
% 9.78/3.76  tff(c_480, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_468])).
% 9.78/3.76  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.78/3.76  tff(c_524, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_480, c_2])).
% 9.78/3.76  tff(c_547, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_524])).
% 9.78/3.76  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.78/3.76  tff(c_1537, plain, (![C_165, D_166, E_163, A_161, B_162, F_164]: (m1_subset_1(k1_partfun1(A_161, B_162, C_165, D_166, E_163, F_164), k1_zfmisc_1(k2_zfmisc_1(A_161, D_166))) | ~m1_subset_1(F_164, k1_zfmisc_1(k2_zfmisc_1(C_165, D_166))) | ~v1_funct_1(F_164) | ~m1_subset_1(E_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))) | ~v1_funct_1(E_163))), inference(cnfTransformation, [status(thm)], [f_136])).
% 9.78/3.76  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.78/3.76  tff(c_839, plain, (![D_121, C_122, A_123, B_124]: (D_121=C_122 | ~r2_relset_1(A_123, B_124, C_122, D_121) | ~m1_subset_1(D_121, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.78/3.76  tff(c_847, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_839])).
% 9.78/3.76  tff(c_862, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_847])).
% 9.78/3.76  tff(c_1021, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_862])).
% 9.78/3.76  tff(c_1550, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1537, c_1021])).
% 9.78/3.76  tff(c_1572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_1550])).
% 9.78/3.76  tff(c_1573, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_862])).
% 9.78/3.76  tff(c_2094, plain, (![F_190, A_194, E_189, B_193, D_191, C_192]: (k1_partfun1(A_194, B_193, C_192, D_191, E_189, F_190)=k5_relat_1(E_189, F_190) | ~m1_subset_1(F_190, k1_zfmisc_1(k2_zfmisc_1(C_192, D_191))) | ~v1_funct_1(F_190) | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(A_194, B_193))) | ~v1_funct_1(E_189))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.78/3.76  tff(c_2100, plain, (![A_194, B_193, E_189]: (k1_partfun1(A_194, B_193, '#skF_2', '#skF_1', E_189, '#skF_4')=k5_relat_1(E_189, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(A_194, B_193))) | ~v1_funct_1(E_189))), inference(resolution, [status(thm)], [c_72, c_2094])).
% 9.78/3.76  tff(c_2275, plain, (![A_206, B_207, E_208]: (k1_partfun1(A_206, B_207, '#skF_2', '#skF_1', E_208, '#skF_4')=k5_relat_1(E_208, '#skF_4') | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))) | ~v1_funct_1(E_208))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2100])).
% 9.78/3.76  tff(c_2284, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_2275])).
% 9.78/3.76  tff(c_2292, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1573, c_2284])).
% 9.78/3.76  tff(c_70, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.78/3.76  tff(c_483, plain, (![A_102, B_103, C_104]: (k2_relset_1(A_102, B_103, C_104)=k2_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.78/3.76  tff(c_489, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_483])).
% 9.78/3.76  tff(c_496, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_489])).
% 9.78/3.76  tff(c_22, plain, (![A_18]: (k5_relat_1(A_18, k6_relat_1(k2_relat_1(A_18)))=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.78/3.76  tff(c_87, plain, (![A_18]: (k5_relat_1(A_18, k6_partfun1(k2_relat_1(A_18)))=A_18 | ~v1_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_22])).
% 9.78/3.76  tff(c_501, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_496, c_87])).
% 9.78/3.76  tff(c_505, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_501])).
% 9.78/3.76  tff(c_612, plain, (![A_111, B_112, C_113]: (k5_relat_1(k5_relat_1(A_111, B_112), C_113)=k5_relat_1(A_111, k5_relat_1(B_112, C_113)) | ~v1_relat_1(C_113) | ~v1_relat_1(B_112) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.78/3.76  tff(c_637, plain, (![C_113]: (k5_relat_1('#skF_3', k5_relat_1(k6_partfun1('#skF_2'), C_113))=k5_relat_1('#skF_3', C_113) | ~v1_relat_1(C_113) | ~v1_relat_1(k6_partfun1('#skF_2')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_505, c_612])).
% 9.78/3.76  tff(c_665, plain, (![C_114]: (k5_relat_1('#skF_3', k5_relat_1(k6_partfun1('#skF_2'), C_114))=k5_relat_1('#skF_3', C_114) | ~v1_relat_1(C_114))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_148, c_637])).
% 9.78/3.76  tff(c_753, plain, (![B_119]: (k5_relat_1('#skF_3', k7_relat_1(B_119, '#skF_2'))=k5_relat_1('#skF_3', B_119) | ~v1_relat_1(B_119) | ~v1_relat_1(B_119))), inference(superposition, [status(thm), theory('equality')], [c_86, c_665])).
% 9.78/3.76  tff(c_14, plain, (![A_7, B_9]: (r1_tarski(k1_relat_1(k5_relat_1(A_7, B_9)), k1_relat_1(A_7)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.78/3.76  tff(c_762, plain, (![B_119]: (r1_tarski(k1_relat_1(k5_relat_1('#skF_3', B_119)), k1_relat_1('#skF_3')) | ~v1_relat_1(k7_relat_1(B_119, '#skF_2')) | ~v1_relat_1('#skF_3') | ~v1_relat_1(B_119) | ~v1_relat_1(B_119))), inference(superposition, [status(thm), theory('equality')], [c_753, c_14])).
% 9.78/3.76  tff(c_781, plain, (![B_119]: (r1_tarski(k1_relat_1(k5_relat_1('#skF_3', B_119)), k1_relat_1('#skF_3')) | ~v1_relat_1(k7_relat_1(B_119, '#skF_2')) | ~v1_relat_1(B_119))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_762])).
% 9.78/3.76  tff(c_2302, plain, (r1_tarski(k1_relat_1(k6_partfun1('#skF_1')), k1_relat_1('#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2292, c_781])).
% 9.78/3.76  tff(c_2317, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_150, c_295, c_89, c_2302])).
% 9.78/3.76  tff(c_2319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_547, c_2317])).
% 9.78/3.76  tff(c_2320, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_524])).
% 9.78/3.76  tff(c_36, plain, (![A_23]: (k5_relat_1(A_23, k2_funct_1(A_23))=k6_relat_1(k1_relat_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.78/3.76  tff(c_84, plain, (![A_23]: (k5_relat_1(A_23, k2_funct_1(A_23))=k6_partfun1(k1_relat_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_36])).
% 9.78/3.76  tff(c_2327, plain, (![B_9]: (r1_tarski(k1_relat_1(k5_relat_1('#skF_3', B_9)), '#skF_1') | ~v1_relat_1(B_9) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2320, c_14])).
% 9.78/3.76  tff(c_2399, plain, (![B_213]: (r1_tarski(k1_relat_1(k5_relat_1('#skF_3', B_213)), '#skF_1') | ~v1_relat_1(B_213))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_2327])).
% 9.78/3.76  tff(c_2660, plain, (![B_229]: (k1_relat_1(k5_relat_1('#skF_3', B_229))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k5_relat_1('#skF_3', B_229))) | ~v1_relat_1(B_229))), inference(resolution, [status(thm)], [c_2399, c_2])).
% 9.78/3.76  tff(c_2664, plain, (k1_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_84, c_2660])).
% 9.78/3.76  tff(c_2673, plain, (k1_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')))='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_82, c_66, c_6, c_2320, c_89, c_2664])).
% 9.78/3.76  tff(c_2743, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2673])).
% 9.78/3.76  tff(c_2746, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_2743])).
% 9.78/3.76  tff(c_2750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149, c_82, c_2746])).
% 9.78/3.76  tff(c_2752, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2673])).
% 9.78/3.76  tff(c_30, plain, (![A_22]: (k2_relat_1(k2_funct_1(A_22))=k1_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.78/3.76  tff(c_215, plain, (![B_79, A_80]: (v4_relat_1(B_79, A_80) | ~r1_tarski(k1_relat_1(B_79), A_80) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.78/3.76  tff(c_221, plain, (![A_17, A_80]: (v4_relat_1(k6_partfun1(A_17), A_80) | ~r1_tarski(A_17, A_80) | ~v1_relat_1(k6_partfun1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_215])).
% 9.78/3.76  tff(c_259, plain, (![A_83, A_84]: (v4_relat_1(k6_partfun1(A_83), A_84) | ~r1_tarski(A_83, A_84))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_221])).
% 9.78/3.76  tff(c_265, plain, (![A_83, A_84]: (k7_relat_1(k6_partfun1(A_83), A_84)=k6_partfun1(A_83) | ~v1_relat_1(k6_partfun1(A_83)) | ~r1_tarski(A_83, A_84))), inference(resolution, [status(thm)], [c_259, c_12])).
% 9.78/3.76  tff(c_269, plain, (![A_83, A_84]: (k7_relat_1(k6_partfun1(A_83), A_84)=k6_partfun1(A_83) | ~r1_tarski(A_83, A_84))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_265])).
% 9.78/3.76  tff(c_20, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.78/3.76  tff(c_88, plain, (![A_17]: (k2_relat_1(k6_partfun1(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_20])).
% 9.78/3.76  tff(c_159, plain, (![A_66, B_67]: (k5_relat_1(k6_partfun1(A_66), B_67)=k7_relat_1(B_67, A_66) | ~v1_relat_1(B_67))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_24])).
% 9.78/3.76  tff(c_166, plain, (![A_66]: (k7_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(A_66))), A_66)=k6_partfun1(A_66) | ~v1_relat_1(k6_partfun1(A_66)) | ~v1_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(A_66)))))), inference(superposition, [status(thm), theory('equality')], [c_159, c_87])).
% 9.78/3.76  tff(c_176, plain, (![A_66]: (k7_relat_1(k6_partfun1(A_66), A_66)=k6_partfun1(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_88, c_148, c_88, c_166])).
% 9.78/3.76  tff(c_2751, plain, (k1_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')))='#skF_1'), inference(splitRight, [status(thm)], [c_2673])).
% 9.78/3.76  tff(c_229, plain, (![B_79]: (v4_relat_1(B_79, k1_relat_1(B_79)) | ~v1_relat_1(B_79))), inference(resolution, [status(thm)], [c_6, c_215])).
% 9.78/3.76  tff(c_2777, plain, (v4_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')), '#skF_1') | ~v1_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2751, c_229])).
% 9.78/3.76  tff(c_2914, plain, (~v1_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_2777])).
% 9.78/3.76  tff(c_2917, plain, (~v1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_84, c_2914])).
% 9.78/3.76  tff(c_2920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149, c_82, c_66, c_148, c_2320, c_2917])).
% 9.78/3.76  tff(c_2922, plain, (v1_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_2777])).
% 9.78/3.76  tff(c_2921, plain, (v4_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')), '#skF_1')), inference(splitRight, [status(thm)], [c_2777])).
% 9.78/3.76  tff(c_2977, plain, (k7_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')), '#skF_1')=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2921, c_12])).
% 9.78/3.76  tff(c_2983, plain, (k7_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')), '#skF_1')=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2922, c_2977])).
% 9.78/3.76  tff(c_2999, plain, (k7_relat_1(k6_partfun1(k1_relat_1('#skF_3')), '#skF_1')=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_84, c_2983])).
% 9.78/3.76  tff(c_3009, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_82, c_66, c_176, c_2320, c_2999])).
% 9.78/3.76  tff(c_16, plain, (![A_10, B_14, C_16]: (k5_relat_1(k5_relat_1(A_10, B_14), C_16)=k5_relat_1(A_10, k5_relat_1(B_14, C_16)) | ~v1_relat_1(C_16) | ~v1_relat_1(B_14) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.78/3.76  tff(c_3021, plain, (![C_16]: (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), C_16))=k5_relat_1(k6_partfun1('#skF_1'), C_16) | ~v1_relat_1(C_16) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3009, c_16])).
% 9.78/3.76  tff(c_3148, plain, (![C_242]: (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), C_242))=k5_relat_1(k6_partfun1('#skF_1'), C_242) | ~v1_relat_1(C_242))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_2752, c_3021])).
% 9.78/3.76  tff(c_3181, plain, (k5_relat_1(k6_partfun1('#skF_1'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_3148])).
% 9.78/3.76  tff(c_3193, plain, (k5_relat_1(k6_partfun1('#skF_1'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2752, c_148, c_3009, c_3181])).
% 9.78/3.76  tff(c_3243, plain, (k7_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))), '#skF_1')=k6_partfun1('#skF_1') | ~v1_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_3193, c_86])).
% 9.78/3.76  tff(c_3261, plain, (k7_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))), '#skF_1')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_3243])).
% 9.78/3.76  tff(c_3729, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))=k6_partfun1('#skF_1') | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_269, c_3261])).
% 9.78/3.76  tff(c_3811, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(splitLeft, [status(thm)], [c_3729])).
% 9.78/3.76  tff(c_3814, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_3811])).
% 9.78/3.76  tff(c_3817, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149, c_82, c_66, c_6, c_2320, c_3814])).
% 9.78/3.76  tff(c_3818, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_3729])).
% 9.78/3.76  tff(c_3885, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3818, c_87])).
% 9.78/3.76  tff(c_3909, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2752, c_3885])).
% 9.78/3.76  tff(c_3545, plain, (![A_258, F_254, C_256, E_253, D_255, B_257]: (k1_partfun1(A_258, B_257, C_256, D_255, E_253, F_254)=k5_relat_1(E_253, F_254) | ~m1_subset_1(F_254, k1_zfmisc_1(k2_zfmisc_1(C_256, D_255))) | ~v1_funct_1(F_254) | ~m1_subset_1(E_253, k1_zfmisc_1(k2_zfmisc_1(A_258, B_257))) | ~v1_funct_1(E_253))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.78/3.76  tff(c_3551, plain, (![A_258, B_257, E_253]: (k1_partfun1(A_258, B_257, '#skF_2', '#skF_1', E_253, '#skF_4')=k5_relat_1(E_253, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_253, k1_zfmisc_1(k2_zfmisc_1(A_258, B_257))) | ~v1_funct_1(E_253))), inference(resolution, [status(thm)], [c_72, c_3545])).
% 9.78/3.76  tff(c_3619, plain, (![A_268, B_269, E_270]: (k1_partfun1(A_268, B_269, '#skF_2', '#skF_1', E_270, '#skF_4')=k5_relat_1(E_270, '#skF_4') | ~m1_subset_1(E_270, k1_zfmisc_1(k2_zfmisc_1(A_268, B_269))) | ~v1_funct_1(E_270))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3551])).
% 9.78/3.76  tff(c_3628, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_3619])).
% 9.78/3.76  tff(c_3636, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3628])).
% 9.78/3.76  tff(c_52, plain, (![D_41, B_39, A_38, F_43, E_42, C_40]: (m1_subset_1(k1_partfun1(A_38, B_39, C_40, D_41, E_42, F_43), k1_zfmisc_1(k2_zfmisc_1(A_38, D_41))) | ~m1_subset_1(F_43, k1_zfmisc_1(k2_zfmisc_1(C_40, D_41))) | ~v1_funct_1(F_43) | ~m1_subset_1(E_42, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_1(E_42))), inference(cnfTransformation, [status(thm)], [f_136])).
% 9.78/3.76  tff(c_3645, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3636, c_52])).
% 9.78/3.76  tff(c_3649, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_3645])).
% 9.78/3.76  tff(c_3124, plain, (![D_238, C_239, A_240, B_241]: (D_238=C_239 | ~r2_relset_1(A_240, B_241, C_239, D_238) | ~m1_subset_1(D_238, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.78/3.76  tff(c_3132, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_3124])).
% 9.78/3.76  tff(c_3147, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_3132])).
% 9.78/3.76  tff(c_3267, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_3147])).
% 9.78/3.76  tff(c_3704, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3649, c_3636, c_3267])).
% 9.78/3.76  tff(c_3705, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_3147])).
% 9.78/3.76  tff(c_3991, plain, (![F_282, C_284, B_285, E_281, D_283, A_286]: (k1_partfun1(A_286, B_285, C_284, D_283, E_281, F_282)=k5_relat_1(E_281, F_282) | ~m1_subset_1(F_282, k1_zfmisc_1(k2_zfmisc_1(C_284, D_283))) | ~v1_funct_1(F_282) | ~m1_subset_1(E_281, k1_zfmisc_1(k2_zfmisc_1(A_286, B_285))) | ~v1_funct_1(E_281))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.78/3.76  tff(c_3997, plain, (![A_286, B_285, E_281]: (k1_partfun1(A_286, B_285, '#skF_2', '#skF_1', E_281, '#skF_4')=k5_relat_1(E_281, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_281, k1_zfmisc_1(k2_zfmisc_1(A_286, B_285))) | ~v1_funct_1(E_281))), inference(resolution, [status(thm)], [c_72, c_3991])).
% 9.78/3.76  tff(c_4516, plain, (![A_303, B_304, E_305]: (k1_partfun1(A_303, B_304, '#skF_2', '#skF_1', E_305, '#skF_4')=k5_relat_1(E_305, '#skF_4') | ~m1_subset_1(E_305, k1_zfmisc_1(k2_zfmisc_1(A_303, B_304))) | ~v1_funct_1(E_305))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3997])).
% 9.78/3.76  tff(c_4531, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_4516])).
% 9.78/3.76  tff(c_4545, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3705, c_4531])).
% 9.78/3.76  tff(c_34, plain, (![A_23]: (k5_relat_1(k2_funct_1(A_23), A_23)=k6_relat_1(k2_relat_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.78/3.76  tff(c_85, plain, (![A_23]: (k5_relat_1(k2_funct_1(A_23), A_23)=k6_partfun1(k2_relat_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_34])).
% 9.78/3.76  tff(c_2800, plain, (![A_231, B_232, C_233]: (k5_relat_1(k5_relat_1(A_231, B_232), C_233)=k5_relat_1(A_231, k5_relat_1(B_232, C_233)) | ~v1_relat_1(C_233) | ~v1_relat_1(B_232) | ~v1_relat_1(A_231))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.78/3.76  tff(c_8801, plain, (![A_382, C_383]: (k5_relat_1(k6_partfun1(k2_relat_1(A_382)), C_383)=k5_relat_1(k2_funct_1(A_382), k5_relat_1(A_382, C_383)) | ~v1_relat_1(C_383) | ~v1_relat_1(A_382) | ~v1_relat_1(k2_funct_1(A_382)) | ~v2_funct_1(A_382) | ~v1_funct_1(A_382) | ~v1_relat_1(A_382))), inference(superposition, [status(thm), theory('equality')], [c_85, c_2800])).
% 9.78/3.76  tff(c_9024, plain, (![C_383]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_383))=k5_relat_1(k6_partfun1('#skF_2'), C_383) | ~v1_relat_1(C_383) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_496, c_8801])).
% 9.78/3.76  tff(c_13327, plain, (![C_492]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_492))=k5_relat_1(k6_partfun1('#skF_2'), C_492) | ~v1_relat_1(C_492))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_82, c_66, c_2752, c_149, c_9024])).
% 9.78/3.76  tff(c_13441, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4545, c_13327])).
% 9.78/3.76  tff(c_13520, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_3909, c_13441])).
% 9.78/3.76  tff(c_13792, plain, (k7_relat_1('#skF_4', '#skF_2')=k2_funct_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13520, c_86])).
% 9.78/3.76  tff(c_13833, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_295, c_13792])).
% 9.78/3.76  tff(c_13835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_13833])).
% 9.78/3.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.78/3.76  
% 9.78/3.76  Inference rules
% 9.78/3.76  ----------------------
% 9.78/3.76  #Ref     : 0
% 9.78/3.76  #Sup     : 2902
% 9.78/3.76  #Fact    : 0
% 9.78/3.76  #Define  : 0
% 9.78/3.76  #Split   : 20
% 9.78/3.76  #Chain   : 0
% 9.78/3.76  #Close   : 0
% 9.78/3.76  
% 9.78/3.76  Ordering : KBO
% 9.78/3.76  
% 9.78/3.76  Simplification rules
% 9.78/3.76  ----------------------
% 9.78/3.76  #Subsume      : 212
% 9.78/3.76  #Demod        : 5381
% 9.78/3.76  #Tautology    : 1017
% 9.78/3.76  #SimpNegUnit  : 3
% 9.78/3.76  #BackRed      : 39
% 9.78/3.76  
% 9.78/3.76  #Partial instantiations: 0
% 9.78/3.76  #Strategies tried      : 1
% 9.78/3.76  
% 9.78/3.76  Timing (in seconds)
% 9.78/3.76  ----------------------
% 9.78/3.77  Preprocessing        : 0.36
% 9.78/3.77  Parsing              : 0.19
% 9.78/3.77  CNF conversion       : 0.02
% 9.78/3.77  Main loop            : 2.63
% 9.78/3.77  Inferencing          : 0.71
% 9.78/3.77  Reduction            : 1.27
% 9.78/3.77  Demodulation         : 1.05
% 9.78/3.77  BG Simplification    : 0.08
% 9.78/3.77  Subsumption          : 0.44
% 9.78/3.77  Abstraction          : 0.10
% 9.78/3.77  MUC search           : 0.00
% 9.78/3.77  Cooper               : 0.00
% 9.78/3.77  Total                : 3.04
% 9.78/3.77  Index Insertion      : 0.00
% 9.78/3.77  Index Deletion       : 0.00
% 9.78/3.77  Index Matching       : 0.00
% 9.78/3.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
