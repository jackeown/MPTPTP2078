%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:56 EST 2020

% Result     : Theorem 7.27s
% Output     : CNFRefutation 7.27s
% Verified   : 
% Statistics : Number of formulae       :  202 (2394 expanded)
%              Number of leaves         :   55 ( 873 expanded)
%              Depth                    :   23
%              Number of atoms          :  427 (7795 expanded)
%              Number of equality atoms :  128 (2632 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_234,negated_conjecture,(
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

tff(f_147,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_153,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_191,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_157,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_179,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_167,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_165,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_189,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_208,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_125,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_135,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(c_76,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_88,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_146,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_159,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_146])).

tff(c_190,plain,(
    ! [C_82,A_83,B_84] :
      ( v4_relat_1(C_82,A_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_202,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_190])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k1_relat_1(B_4),A_3)
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_94,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_158,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_146])).

tff(c_98,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_72,plain,(
    ! [A_59] : k6_relat_1(A_59) = k6_partfun1(A_59) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_34,plain,(
    ! [A_24] : v2_funct_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_102,plain,(
    ! [A_24] : v2_funct_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_34])).

tff(c_86,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_707,plain,(
    ! [A_128,B_129,C_130] :
      ( k2_relset_1(A_128,B_129,C_130) = k2_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_713,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_707])).

tff(c_720,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_713])).

tff(c_3199,plain,(
    ! [F_214,A_213,D_216,B_217,C_218,E_215] :
      ( m1_subset_1(k1_partfun1(A_213,B_217,C_218,D_216,E_215,F_214),k1_zfmisc_1(k2_zfmisc_1(A_213,D_216)))
      | ~ m1_subset_1(F_214,k1_zfmisc_1(k2_zfmisc_1(C_218,D_216)))
      | ~ v1_funct_1(F_214)
      | ~ m1_subset_1(E_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_217)))
      | ~ v1_funct_1(E_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_64,plain,(
    ! [A_46] : m1_subset_1(k6_relat_1(A_46),k1_zfmisc_1(k2_zfmisc_1(A_46,A_46))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_99,plain,(
    ! [A_46] : m1_subset_1(k6_partfun1(A_46),k1_zfmisc_1(k2_zfmisc_1(A_46,A_46))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_64])).

tff(c_84,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_2392,plain,(
    ! [D_176,C_177,A_178,B_179] :
      ( D_176 = C_177
      | ~ r2_relset_1(A_178,B_179,C_177,D_176)
      | ~ m1_subset_1(D_176,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179)))
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_2400,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_84,c_2392])).

tff(c_2415,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_2400])).

tff(c_2467,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2415])).

tff(c_3212,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3199,c_2467])).

tff(c_3234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_94,c_92,c_88,c_3212])).

tff(c_3235,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2415])).

tff(c_3835,plain,(
    ! [A_241,D_243,E_242,B_244,F_245,C_240] :
      ( k1_partfun1(A_241,B_244,C_240,D_243,E_242,F_245) = k5_relat_1(E_242,F_245)
      | ~ m1_subset_1(F_245,k1_zfmisc_1(k2_zfmisc_1(C_240,D_243)))
      | ~ v1_funct_1(F_245)
      | ~ m1_subset_1(E_242,k1_zfmisc_1(k2_zfmisc_1(A_241,B_244)))
      | ~ v1_funct_1(E_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_3841,plain,(
    ! [A_241,B_244,E_242] :
      ( k1_partfun1(A_241,B_244,'#skF_2','#skF_1',E_242,'#skF_4') = k5_relat_1(E_242,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_242,k1_zfmisc_1(k2_zfmisc_1(A_241,B_244)))
      | ~ v1_funct_1(E_242) ) ),
    inference(resolution,[status(thm)],[c_88,c_3835])).

tff(c_4895,plain,(
    ! [A_270,B_271,E_272] :
      ( k1_partfun1(A_270,B_271,'#skF_2','#skF_1',E_272,'#skF_4') = k5_relat_1(E_272,'#skF_4')
      | ~ m1_subset_1(E_272,k1_zfmisc_1(k2_zfmisc_1(A_270,B_271)))
      | ~ v1_funct_1(E_272) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_3841])).

tff(c_4907,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_4895])).

tff(c_4918,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_3235,c_4907])).

tff(c_38,plain,(
    ! [A_27,B_29] :
      ( v2_funct_1(A_27)
      | k2_relat_1(B_29) != k1_relat_1(A_27)
      | ~ v2_funct_1(k5_relat_1(B_29,A_27))
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4934,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4918,c_38])).

tff(c_4953,plain,
    ( v2_funct_1('#skF_4')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_92,c_158,c_98,c_102,c_720,c_4934])).

tff(c_4961,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4953])).

tff(c_201,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_94,c_190])).

tff(c_261,plain,(
    ! [B_97,A_98] :
      ( k7_relat_1(B_97,A_98) = B_97
      | ~ v4_relat_1(B_97,A_98)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_273,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_201,c_261])).

tff(c_283,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_273])).

tff(c_326,plain,(
    ! [B_103,A_104] :
      ( k2_relat_1(k7_relat_1(B_103,A_104)) = k9_relat_1(B_103,A_104)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_341,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_326])).

tff(c_350,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_341])).

tff(c_722,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_350])).

tff(c_20,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_107,plain,(
    ! [A_19] : k1_relat_1(k6_partfun1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_20])).

tff(c_14,plain,(
    ! [A_7,B_9] :
      ( k10_relat_1(A_7,k1_relat_1(B_9)) = k1_relat_1(k5_relat_1(A_7,B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_973,plain,(
    ! [B_139,A_140] :
      ( k9_relat_1(B_139,k10_relat_1(B_139,A_140)) = A_140
      | ~ r1_tarski(A_140,k2_relat_1(B_139))
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_975,plain,(
    ! [A_140] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_140)) = A_140
      | ~ r1_tarski(A_140,'#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_720,c_973])).

tff(c_994,plain,(
    ! [A_141] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_141)) = A_141
      | ~ r1_tarski(A_141,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_98,c_975])).

tff(c_1011,plain,(
    ! [B_9] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_9))) = k1_relat_1(B_9)
      | ~ r1_tarski(k1_relat_1(B_9),'#skF_2')
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_994])).

tff(c_1019,plain,(
    ! [B_9] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_9))) = k1_relat_1(B_9)
      | ~ r1_tarski(k1_relat_1(B_9),'#skF_2')
      | ~ v1_relat_1(B_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_1011])).

tff(c_4943,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4918,c_1019])).

tff(c_4959,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_722,c_107,c_4943])).

tff(c_4962,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_4961,c_4959])).

tff(c_4965,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_4962])).

tff(c_4969,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_202,c_4965])).

tff(c_4971,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4953])).

tff(c_32,plain,(
    ! [A_24] : v1_relat_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_103,plain,(
    ! [A_24] : v1_relat_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_32])).

tff(c_90,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_96,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_482,plain,(
    ! [A_112,B_113,D_114] :
      ( r2_relset_1(A_112,B_113,D_114,D_114)
      | ~ m1_subset_1(D_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_489,plain,(
    ! [A_46] : r2_relset_1(A_46,A_46,k6_partfun1(A_46),k6_partfun1(A_46)) ),
    inference(resolution,[status(thm)],[c_99,c_482])).

tff(c_721,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_707])).

tff(c_4591,plain,(
    ! [A_263,B_264,C_265,D_266] :
      ( k2_relset_1(A_263,B_264,C_265) = B_264
      | ~ r2_relset_1(B_264,B_264,k1_partfun1(B_264,A_263,A_263,B_264,D_266,C_265),k6_partfun1(B_264))
      | ~ m1_subset_1(D_266,k1_zfmisc_1(k2_zfmisc_1(B_264,A_263)))
      | ~ v1_funct_2(D_266,B_264,A_263)
      | ~ v1_funct_1(D_266)
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_263,B_264)))
      | ~ v1_funct_2(C_265,A_263,B_264)
      | ~ v1_funct_1(C_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_4594,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3235,c_4591])).

tff(c_4596,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_98,c_96,c_94,c_489,c_721,c_4594])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [B_22,A_21] :
      ( k5_relat_1(B_22,k6_relat_1(A_21)) = B_22
      | ~ r1_tarski(k2_relat_1(B_22),A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_523,plain,(
    ! [B_117,A_118] :
      ( k5_relat_1(B_117,k6_partfun1(A_118)) = B_117
      | ~ r1_tarski(k2_relat_1(B_117),A_118)
      | ~ v1_relat_1(B_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_26])).

tff(c_536,plain,(
    ! [B_117] :
      ( k5_relat_1(B_117,k6_partfun1(k2_relat_1(B_117))) = B_117
      | ~ v1_relat_1(B_117) ) ),
    inference(resolution,[status(thm)],[c_6,c_523])).

tff(c_4613,plain,
    ( k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4596,c_536])).

tff(c_4628,plain,(
    k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_4613])).

tff(c_24,plain,(
    ! [A_20] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_20)),A_20) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_105,plain,(
    ! [A_20] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_20)),A_20) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_24])).

tff(c_1465,plain,(
    ! [A_154,B_155,C_156] :
      ( k5_relat_1(k5_relat_1(A_154,B_155),C_156) = k5_relat_1(A_154,k5_relat_1(B_155,C_156))
      | ~ v1_relat_1(C_156)
      | ~ v1_relat_1(B_155)
      | ~ v1_relat_1(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1524,plain,(
    ! [A_20,C_156] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_20)),k5_relat_1(A_20,C_156)) = k5_relat_1(A_20,C_156)
      | ~ v1_relat_1(C_156)
      | ~ v1_relat_1(A_20)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_20)))
      | ~ v1_relat_1(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_1465])).

tff(c_1546,plain,(
    ! [A_20,C_156] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_20)),k5_relat_1(A_20,C_156)) = k5_relat_1(A_20,C_156)
      | ~ v1_relat_1(C_156)
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_1524])).

tff(c_4662,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),'#skF_4') = k5_relat_1('#skF_4',k6_partfun1('#skF_1'))
    | ~ v1_relat_1(k6_partfun1('#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4628,c_1546])).

tff(c_4678,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_103,c_4628,c_4662])).

tff(c_5047,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4971,c_4678])).

tff(c_4928,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_1')) = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4918,c_1546])).

tff(c_4949,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_1')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_159,c_4918,c_4928])).

tff(c_22,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_106,plain,(
    ! [A_19] : k2_relat_1(k6_partfun1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_22])).

tff(c_529,plain,(
    ! [A_19,A_118] :
      ( k5_relat_1(k6_partfun1(A_19),k6_partfun1(A_118)) = k6_partfun1(A_19)
      | ~ r1_tarski(A_19,A_118)
      | ~ v1_relat_1(k6_partfun1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_523])).

tff(c_535,plain,(
    ! [A_19,A_118] :
      ( k5_relat_1(k6_partfun1(A_19),k6_partfun1(A_118)) = k6_partfun1(A_19)
      | ~ r1_tarski(A_19,A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_529])).

tff(c_620,plain,(
    ! [A_123,B_124] :
      ( k10_relat_1(A_123,k1_relat_1(B_124)) = k1_relat_1(k5_relat_1(A_123,B_124))
      | ~ v1_relat_1(B_124)
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_632,plain,(
    ! [A_123,A_19] :
      ( k1_relat_1(k5_relat_1(A_123,k6_partfun1(A_19))) = k10_relat_1(A_123,A_19)
      | ~ v1_relat_1(k6_partfun1(A_19))
      | ~ v1_relat_1(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_620])).

tff(c_637,plain,(
    ! [A_125,A_126] :
      ( k1_relat_1(k5_relat_1(A_125,k6_partfun1(A_126))) = k10_relat_1(A_125,A_126)
      | ~ v1_relat_1(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_632])).

tff(c_667,plain,(
    ! [A_19,A_118] :
      ( k10_relat_1(k6_partfun1(A_19),A_118) = k1_relat_1(k6_partfun1(A_19))
      | ~ v1_relat_1(k6_partfun1(A_19))
      | ~ r1_tarski(A_19,A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_637])).

tff(c_808,plain,(
    ! [A_133,A_134] :
      ( k10_relat_1(k6_partfun1(A_133),A_134) = A_133
      | ~ r1_tarski(A_133,A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_107,c_667])).

tff(c_829,plain,(
    ! [A_133,B_9] :
      ( k1_relat_1(k5_relat_1(k6_partfun1(A_133),B_9)) = A_133
      | ~ r1_tarski(A_133,k1_relat_1(B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(k6_partfun1(A_133)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_808])).

tff(c_841,plain,(
    ! [A_133,B_9] :
      ( k1_relat_1(k5_relat_1(k6_partfun1(A_133),B_9)) = A_133
      | ~ r1_tarski(A_133,k1_relat_1(B_9))
      | ~ v1_relat_1(B_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_829])).

tff(c_5313,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(k6_partfun1('#skF_1')))
    | ~ v1_relat_1(k6_partfun1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4949,c_841])).

tff(c_5344,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_107,c_107,c_5313])).

tff(c_5388,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5344])).

tff(c_5391,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_5388])).

tff(c_5395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_201,c_5391])).

tff(c_5396,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5344])).

tff(c_82,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_42,plain,(
    ! [A_30] :
      ( k2_relat_1(k2_funct_1(A_30)) = k1_relat_1(A_30)
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_30,plain,(
    ! [A_23] :
      ( v1_relat_1(k2_funct_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_670,plain,(
    ! [B_117] :
      ( k10_relat_1(B_117,k2_relat_1(B_117)) = k1_relat_1(B_117)
      | ~ v1_relat_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_637])).

tff(c_1004,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_994])).

tff(c_1015,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_158,c_6,c_720,c_720,c_1004])).

tff(c_48,plain,(
    ! [A_31] :
      ( k5_relat_1(A_31,k2_funct_1(A_31)) = k6_relat_1(k1_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_100,plain,(
    ! [A_31] :
      ( k5_relat_1(A_31,k2_funct_1(A_31)) = k6_partfun1(k1_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_48])).

tff(c_1239,plain,(
    ! [B_150] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_150))) = k1_relat_1(B_150)
      | ~ r1_tarski(k1_relat_1(B_150),'#skF_2')
      | ~ v1_relat_1(B_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_1011])).

tff(c_1249,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_1239])).

tff(c_1267,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_98,c_82,c_1015,c_107,c_1249])).

tff(c_1276,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1267])).

tff(c_1279,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1276])).

tff(c_1283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_98,c_1279])).

tff(c_1285,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1267])).

tff(c_44,plain,(
    ! [A_30] :
      ( k1_relat_1(k2_funct_1(A_30)) = k2_relat_1(A_30)
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1284,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1267])).

tff(c_1286,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1284])).

tff(c_1366,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1286])).

tff(c_1372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_98,c_82,c_6,c_720,c_1366])).

tff(c_1373,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1284])).

tff(c_1405,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1373,c_105])).

tff(c_1430,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1285,c_1405])).

tff(c_1492,plain,(
    ! [C_156] :
      ( k5_relat_1(k6_partfun1('#skF_2'),k5_relat_1(k2_funct_1('#skF_3'),C_156)) = k5_relat_1(k2_funct_1('#skF_3'),C_156)
      | ~ v1_relat_1(C_156)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k6_partfun1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1430,c_1465])).

tff(c_2041,plain,(
    ! [C_172] :
      ( k5_relat_1(k6_partfun1('#skF_2'),k5_relat_1(k2_funct_1('#skF_3'),C_172)) = k5_relat_1(k2_funct_1('#skF_3'),C_172)
      | ~ v1_relat_1(C_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_1285,c_1492])).

tff(c_2077,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_2041])).

tff(c_2094,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1285,c_103,c_1430,c_2077])).

tff(c_2146,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2094])).

tff(c_2164,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_98,c_82,c_2146])).

tff(c_5426,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5396,c_2164])).

tff(c_160,plain,(
    ! [A_78] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_78)),A_78) = A_78
      | ~ v1_relat_1(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_24])).

tff(c_169,plain,(
    ! [A_19] :
      ( k5_relat_1(k6_partfun1(A_19),k6_partfun1(A_19)) = k6_partfun1(A_19)
      | ~ v1_relat_1(k6_partfun1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_160])).

tff(c_173,plain,(
    ! [A_19] : k5_relat_1(k6_partfun1(A_19),k6_partfun1(A_19)) = k6_partfun1(A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_169])).

tff(c_46,plain,(
    ! [A_31] :
      ( k5_relat_1(k2_funct_1(A_31),A_31) = k6_relat_1(k2_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_101,plain,(
    ! [A_31] :
      ( k5_relat_1(k2_funct_1(A_31),A_31) = k6_partfun1(k2_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_46])).

tff(c_2073,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k6_partfun1(k2_relat_1('#skF_3'))) = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_2041])).

tff(c_2092,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_98,c_82,c_158,c_173,c_720,c_2073])).

tff(c_18,plain,(
    ! [A_12,B_16,C_18] :
      ( k5_relat_1(k5_relat_1(A_12,B_16),C_18) = k5_relat_1(A_12,k5_relat_1(B_16,C_18))
      | ~ v1_relat_1(C_18)
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2104,plain,(
    ! [C_18] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_18)) = k5_relat_1(k6_partfun1('#skF_2'),C_18)
      | ~ v1_relat_1(C_18)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2092,c_18])).

tff(c_2118,plain,(
    ! [C_18] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_18)) = k5_relat_1(k6_partfun1('#skF_2'),C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1285,c_158,c_2104])).

tff(c_4931,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4918,c_2118])).

tff(c_4951,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_4931])).

tff(c_6981,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5047,c_5426,c_4951])).

tff(c_6982,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_6981])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:17:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.27/2.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.27/2.48  
% 7.27/2.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.27/2.48  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.27/2.48  
% 7.27/2.48  %Foreground sorts:
% 7.27/2.48  
% 7.27/2.48  
% 7.27/2.48  %Background operators:
% 7.27/2.48  
% 7.27/2.48  
% 7.27/2.48  %Foreground operators:
% 7.27/2.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.27/2.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.27/2.48  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.27/2.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.27/2.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.27/2.48  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.27/2.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.27/2.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.27/2.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.27/2.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.27/2.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.27/2.48  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.27/2.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.27/2.48  tff('#skF_2', type, '#skF_2': $i).
% 7.27/2.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.27/2.48  tff('#skF_3', type, '#skF_3': $i).
% 7.27/2.48  tff('#skF_1', type, '#skF_1': $i).
% 7.27/2.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.27/2.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.27/2.48  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.27/2.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.27/2.48  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.27/2.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.27/2.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.27/2.48  tff('#skF_4', type, '#skF_4': $i).
% 7.27/2.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.27/2.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.27/2.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.27/2.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.27/2.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.27/2.48  
% 7.27/2.51  tff(f_234, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 7.27/2.51  tff(f_147, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.27/2.51  tff(f_153, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.27/2.51  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 7.27/2.51  tff(f_191, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.27/2.51  tff(f_90, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.27/2.51  tff(f_157, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.27/2.51  tff(f_179, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.27/2.51  tff(f_167, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 7.27/2.51  tff(f_165, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.27/2.51  tff(f_189, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.27/2.51  tff(f_115, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 7.27/2.51  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 7.27/2.51  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 7.27/2.51  tff(f_68, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.27/2.51  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 7.27/2.51  tff(f_98, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 7.27/2.51  tff(f_208, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 7.27/2.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.27/2.51  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 7.27/2.51  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 7.27/2.51  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 7.27/2.51  tff(f_125, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 7.27/2.51  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.27/2.51  tff(f_135, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 7.27/2.51  tff(c_76, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.27/2.51  tff(c_88, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.27/2.51  tff(c_146, plain, (![C_75, A_76, B_77]: (v1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.27/2.51  tff(c_159, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_88, c_146])).
% 7.27/2.51  tff(c_190, plain, (![C_82, A_83, B_84]: (v4_relat_1(C_82, A_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 7.27/2.51  tff(c_202, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_88, c_190])).
% 7.27/2.51  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k1_relat_1(B_4), A_3) | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.27/2.51  tff(c_92, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.27/2.51  tff(c_94, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.27/2.51  tff(c_158, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_146])).
% 7.27/2.51  tff(c_98, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.27/2.51  tff(c_72, plain, (![A_59]: (k6_relat_1(A_59)=k6_partfun1(A_59))), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.27/2.51  tff(c_34, plain, (![A_24]: (v2_funct_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.27/2.51  tff(c_102, plain, (![A_24]: (v2_funct_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_34])).
% 7.27/2.51  tff(c_86, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.27/2.51  tff(c_707, plain, (![A_128, B_129, C_130]: (k2_relset_1(A_128, B_129, C_130)=k2_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.27/2.51  tff(c_713, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_707])).
% 7.27/2.51  tff(c_720, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_713])).
% 7.27/2.51  tff(c_3199, plain, (![F_214, A_213, D_216, B_217, C_218, E_215]: (m1_subset_1(k1_partfun1(A_213, B_217, C_218, D_216, E_215, F_214), k1_zfmisc_1(k2_zfmisc_1(A_213, D_216))) | ~m1_subset_1(F_214, k1_zfmisc_1(k2_zfmisc_1(C_218, D_216))) | ~v1_funct_1(F_214) | ~m1_subset_1(E_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_217))) | ~v1_funct_1(E_215))), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.27/2.51  tff(c_64, plain, (![A_46]: (m1_subset_1(k6_relat_1(A_46), k1_zfmisc_1(k2_zfmisc_1(A_46, A_46))))), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.27/2.51  tff(c_99, plain, (![A_46]: (m1_subset_1(k6_partfun1(A_46), k1_zfmisc_1(k2_zfmisc_1(A_46, A_46))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_64])).
% 7.27/2.51  tff(c_84, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.27/2.51  tff(c_2392, plain, (![D_176, C_177, A_178, B_179]: (D_176=C_177 | ~r2_relset_1(A_178, B_179, C_177, D_176) | ~m1_subset_1(D_176, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.27/2.51  tff(c_2400, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_84, c_2392])).
% 7.27/2.51  tff(c_2415, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_2400])).
% 7.27/2.51  tff(c_2467, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2415])).
% 7.27/2.51  tff(c_3212, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_3199, c_2467])).
% 7.27/2.51  tff(c_3234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_94, c_92, c_88, c_3212])).
% 7.27/2.51  tff(c_3235, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2415])).
% 7.27/2.51  tff(c_3835, plain, (![A_241, D_243, E_242, B_244, F_245, C_240]: (k1_partfun1(A_241, B_244, C_240, D_243, E_242, F_245)=k5_relat_1(E_242, F_245) | ~m1_subset_1(F_245, k1_zfmisc_1(k2_zfmisc_1(C_240, D_243))) | ~v1_funct_1(F_245) | ~m1_subset_1(E_242, k1_zfmisc_1(k2_zfmisc_1(A_241, B_244))) | ~v1_funct_1(E_242))), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.27/2.51  tff(c_3841, plain, (![A_241, B_244, E_242]: (k1_partfun1(A_241, B_244, '#skF_2', '#skF_1', E_242, '#skF_4')=k5_relat_1(E_242, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_242, k1_zfmisc_1(k2_zfmisc_1(A_241, B_244))) | ~v1_funct_1(E_242))), inference(resolution, [status(thm)], [c_88, c_3835])).
% 7.27/2.51  tff(c_4895, plain, (![A_270, B_271, E_272]: (k1_partfun1(A_270, B_271, '#skF_2', '#skF_1', E_272, '#skF_4')=k5_relat_1(E_272, '#skF_4') | ~m1_subset_1(E_272, k1_zfmisc_1(k2_zfmisc_1(A_270, B_271))) | ~v1_funct_1(E_272))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_3841])).
% 7.27/2.51  tff(c_4907, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_4895])).
% 7.27/2.51  tff(c_4918, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_3235, c_4907])).
% 7.27/2.51  tff(c_38, plain, (![A_27, B_29]: (v2_funct_1(A_27) | k2_relat_1(B_29)!=k1_relat_1(A_27) | ~v2_funct_1(k5_relat_1(B_29, A_27)) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.27/2.51  tff(c_4934, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4918, c_38])).
% 7.27/2.51  tff(c_4953, plain, (v2_funct_1('#skF_4') | k1_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_159, c_92, c_158, c_98, c_102, c_720, c_4934])).
% 7.27/2.51  tff(c_4961, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_4953])).
% 7.27/2.51  tff(c_201, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_94, c_190])).
% 7.27/2.51  tff(c_261, plain, (![B_97, A_98]: (k7_relat_1(B_97, A_98)=B_97 | ~v4_relat_1(B_97, A_98) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.27/2.51  tff(c_273, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_201, c_261])).
% 7.27/2.51  tff(c_283, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_273])).
% 7.27/2.51  tff(c_326, plain, (![B_103, A_104]: (k2_relat_1(k7_relat_1(B_103, A_104))=k9_relat_1(B_103, A_104) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.27/2.51  tff(c_341, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_283, c_326])).
% 7.27/2.51  tff(c_350, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_341])).
% 7.27/2.51  tff(c_722, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_720, c_350])).
% 7.27/2.51  tff(c_20, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.27/2.51  tff(c_107, plain, (![A_19]: (k1_relat_1(k6_partfun1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_20])).
% 7.27/2.51  tff(c_14, plain, (![A_7, B_9]: (k10_relat_1(A_7, k1_relat_1(B_9))=k1_relat_1(k5_relat_1(A_7, B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.27/2.51  tff(c_973, plain, (![B_139, A_140]: (k9_relat_1(B_139, k10_relat_1(B_139, A_140))=A_140 | ~r1_tarski(A_140, k2_relat_1(B_139)) | ~v1_funct_1(B_139) | ~v1_relat_1(B_139))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.27/2.51  tff(c_975, plain, (![A_140]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_140))=A_140 | ~r1_tarski(A_140, '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_720, c_973])).
% 7.27/2.51  tff(c_994, plain, (![A_141]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_141))=A_141 | ~r1_tarski(A_141, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_98, c_975])).
% 7.27/2.51  tff(c_1011, plain, (![B_9]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_9)))=k1_relat_1(B_9) | ~r1_tarski(k1_relat_1(B_9), '#skF_2') | ~v1_relat_1(B_9) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_994])).
% 7.27/2.51  tff(c_1019, plain, (![B_9]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_9)))=k1_relat_1(B_9) | ~r1_tarski(k1_relat_1(B_9), '#skF_2') | ~v1_relat_1(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_1011])).
% 7.27/2.51  tff(c_4943, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1')))=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4918, c_1019])).
% 7.27/2.51  tff(c_4959, plain, (k1_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_722, c_107, c_4943])).
% 7.27/2.51  tff(c_4962, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_4961, c_4959])).
% 7.27/2.51  tff(c_4965, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_4962])).
% 7.27/2.51  tff(c_4969, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_202, c_4965])).
% 7.27/2.51  tff(c_4971, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_4953])).
% 7.27/2.51  tff(c_32, plain, (![A_24]: (v1_relat_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.27/2.51  tff(c_103, plain, (![A_24]: (v1_relat_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_32])).
% 7.27/2.51  tff(c_90, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.27/2.51  tff(c_96, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.27/2.51  tff(c_482, plain, (![A_112, B_113, D_114]: (r2_relset_1(A_112, B_113, D_114, D_114) | ~m1_subset_1(D_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.27/2.51  tff(c_489, plain, (![A_46]: (r2_relset_1(A_46, A_46, k6_partfun1(A_46), k6_partfun1(A_46)))), inference(resolution, [status(thm)], [c_99, c_482])).
% 7.27/2.51  tff(c_721, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_88, c_707])).
% 7.27/2.51  tff(c_4591, plain, (![A_263, B_264, C_265, D_266]: (k2_relset_1(A_263, B_264, C_265)=B_264 | ~r2_relset_1(B_264, B_264, k1_partfun1(B_264, A_263, A_263, B_264, D_266, C_265), k6_partfun1(B_264)) | ~m1_subset_1(D_266, k1_zfmisc_1(k2_zfmisc_1(B_264, A_263))) | ~v1_funct_2(D_266, B_264, A_263) | ~v1_funct_1(D_266) | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(A_263, B_264))) | ~v1_funct_2(C_265, A_263, B_264) | ~v1_funct_1(C_265))), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.27/2.51  tff(c_4594, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3235, c_4591])).
% 7.27/2.51  tff(c_4596, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_98, c_96, c_94, c_489, c_721, c_4594])).
% 7.27/2.51  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.27/2.51  tff(c_26, plain, (![B_22, A_21]: (k5_relat_1(B_22, k6_relat_1(A_21))=B_22 | ~r1_tarski(k2_relat_1(B_22), A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.27/2.51  tff(c_523, plain, (![B_117, A_118]: (k5_relat_1(B_117, k6_partfun1(A_118))=B_117 | ~r1_tarski(k2_relat_1(B_117), A_118) | ~v1_relat_1(B_117))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_26])).
% 7.27/2.51  tff(c_536, plain, (![B_117]: (k5_relat_1(B_117, k6_partfun1(k2_relat_1(B_117)))=B_117 | ~v1_relat_1(B_117))), inference(resolution, [status(thm)], [c_6, c_523])).
% 7.27/2.51  tff(c_4613, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4596, c_536])).
% 7.27/2.51  tff(c_4628, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_159, c_4613])).
% 7.27/2.51  tff(c_24, plain, (![A_20]: (k5_relat_1(k6_relat_1(k1_relat_1(A_20)), A_20)=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.27/2.51  tff(c_105, plain, (![A_20]: (k5_relat_1(k6_partfun1(k1_relat_1(A_20)), A_20)=A_20 | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_24])).
% 7.27/2.51  tff(c_1465, plain, (![A_154, B_155, C_156]: (k5_relat_1(k5_relat_1(A_154, B_155), C_156)=k5_relat_1(A_154, k5_relat_1(B_155, C_156)) | ~v1_relat_1(C_156) | ~v1_relat_1(B_155) | ~v1_relat_1(A_154))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.27/2.51  tff(c_1524, plain, (![A_20, C_156]: (k5_relat_1(k6_partfun1(k1_relat_1(A_20)), k5_relat_1(A_20, C_156))=k5_relat_1(A_20, C_156) | ~v1_relat_1(C_156) | ~v1_relat_1(A_20) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_20))) | ~v1_relat_1(A_20))), inference(superposition, [status(thm), theory('equality')], [c_105, c_1465])).
% 7.27/2.51  tff(c_1546, plain, (![A_20, C_156]: (k5_relat_1(k6_partfun1(k1_relat_1(A_20)), k5_relat_1(A_20, C_156))=k5_relat_1(A_20, C_156) | ~v1_relat_1(C_156) | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_1524])).
% 7.27/2.51  tff(c_4662, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), '#skF_4')=k5_relat_1('#skF_4', k6_partfun1('#skF_1')) | ~v1_relat_1(k6_partfun1('#skF_1')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4628, c_1546])).
% 7.27/2.51  tff(c_4678, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_159, c_103, c_4628, c_4662])).
% 7.27/2.51  tff(c_5047, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4971, c_4678])).
% 7.27/2.51  tff(c_4928, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_1'))=k5_relat_1('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4918, c_1546])).
% 7.27/2.51  tff(c_4949, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_1'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_159, c_4918, c_4928])).
% 7.27/2.51  tff(c_22, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.27/2.51  tff(c_106, plain, (![A_19]: (k2_relat_1(k6_partfun1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_22])).
% 7.27/2.51  tff(c_529, plain, (![A_19, A_118]: (k5_relat_1(k6_partfun1(A_19), k6_partfun1(A_118))=k6_partfun1(A_19) | ~r1_tarski(A_19, A_118) | ~v1_relat_1(k6_partfun1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_523])).
% 7.27/2.51  tff(c_535, plain, (![A_19, A_118]: (k5_relat_1(k6_partfun1(A_19), k6_partfun1(A_118))=k6_partfun1(A_19) | ~r1_tarski(A_19, A_118))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_529])).
% 7.27/2.51  tff(c_620, plain, (![A_123, B_124]: (k10_relat_1(A_123, k1_relat_1(B_124))=k1_relat_1(k5_relat_1(A_123, B_124)) | ~v1_relat_1(B_124) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.27/2.51  tff(c_632, plain, (![A_123, A_19]: (k1_relat_1(k5_relat_1(A_123, k6_partfun1(A_19)))=k10_relat_1(A_123, A_19) | ~v1_relat_1(k6_partfun1(A_19)) | ~v1_relat_1(A_123))), inference(superposition, [status(thm), theory('equality')], [c_107, c_620])).
% 7.27/2.51  tff(c_637, plain, (![A_125, A_126]: (k1_relat_1(k5_relat_1(A_125, k6_partfun1(A_126)))=k10_relat_1(A_125, A_126) | ~v1_relat_1(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_632])).
% 7.27/2.51  tff(c_667, plain, (![A_19, A_118]: (k10_relat_1(k6_partfun1(A_19), A_118)=k1_relat_1(k6_partfun1(A_19)) | ~v1_relat_1(k6_partfun1(A_19)) | ~r1_tarski(A_19, A_118))), inference(superposition, [status(thm), theory('equality')], [c_535, c_637])).
% 7.27/2.51  tff(c_808, plain, (![A_133, A_134]: (k10_relat_1(k6_partfun1(A_133), A_134)=A_133 | ~r1_tarski(A_133, A_134))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_107, c_667])).
% 7.27/2.51  tff(c_829, plain, (![A_133, B_9]: (k1_relat_1(k5_relat_1(k6_partfun1(A_133), B_9))=A_133 | ~r1_tarski(A_133, k1_relat_1(B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(k6_partfun1(A_133)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_808])).
% 7.27/2.51  tff(c_841, plain, (![A_133, B_9]: (k1_relat_1(k5_relat_1(k6_partfun1(A_133), B_9))=A_133 | ~r1_tarski(A_133, k1_relat_1(B_9)) | ~v1_relat_1(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_829])).
% 7.27/2.51  tff(c_5313, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(k6_partfun1('#skF_1'))) | ~v1_relat_1(k6_partfun1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4949, c_841])).
% 7.27/2.51  tff(c_5344, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_107, c_107, c_5313])).
% 7.27/2.51  tff(c_5388, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_5344])).
% 7.27/2.51  tff(c_5391, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_5388])).
% 7.27/2.51  tff(c_5395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_201, c_5391])).
% 7.27/2.51  tff(c_5396, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_5344])).
% 7.27/2.51  tff(c_82, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.27/2.51  tff(c_42, plain, (![A_30]: (k2_relat_1(k2_funct_1(A_30))=k1_relat_1(A_30) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.27/2.51  tff(c_30, plain, (![A_23]: (v1_relat_1(k2_funct_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.27/2.51  tff(c_670, plain, (![B_117]: (k10_relat_1(B_117, k2_relat_1(B_117))=k1_relat_1(B_117) | ~v1_relat_1(B_117) | ~v1_relat_1(B_117))), inference(superposition, [status(thm), theory('equality')], [c_536, c_637])).
% 7.27/2.51  tff(c_1004, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_670, c_994])).
% 7.27/2.51  tff(c_1015, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_158, c_6, c_720, c_720, c_1004])).
% 7.27/2.51  tff(c_48, plain, (![A_31]: (k5_relat_1(A_31, k2_funct_1(A_31))=k6_relat_1(k1_relat_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.27/2.51  tff(c_100, plain, (![A_31]: (k5_relat_1(A_31, k2_funct_1(A_31))=k6_partfun1(k1_relat_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_48])).
% 7.27/2.51  tff(c_1239, plain, (![B_150]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_150)))=k1_relat_1(B_150) | ~r1_tarski(k1_relat_1(B_150), '#skF_2') | ~v1_relat_1(B_150))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_1011])).
% 7.27/2.51  tff(c_1249, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))))=k1_relat_1(k2_funct_1('#skF_3')) | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_100, c_1239])).
% 7.27/2.51  tff(c_1267, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_98, c_82, c_1015, c_107, c_1249])).
% 7.27/2.51  tff(c_1276, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1267])).
% 7.27/2.51  tff(c_1279, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_1276])).
% 7.27/2.51  tff(c_1283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_98, c_1279])).
% 7.27/2.51  tff(c_1285, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1267])).
% 7.27/2.51  tff(c_44, plain, (![A_30]: (k1_relat_1(k2_funct_1(A_30))=k2_relat_1(A_30) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.27/2.51  tff(c_1284, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_1267])).
% 7.27/2.51  tff(c_1286, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_1284])).
% 7.27/2.51  tff(c_1366, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_44, c_1286])).
% 7.27/2.51  tff(c_1372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_98, c_82, c_6, c_720, c_1366])).
% 7.27/2.51  tff(c_1373, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_1284])).
% 7.27/2.51  tff(c_1405, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1373, c_105])).
% 7.27/2.51  tff(c_1430, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1285, c_1405])).
% 7.27/2.51  tff(c_1492, plain, (![C_156]: (k5_relat_1(k6_partfun1('#skF_2'), k5_relat_1(k2_funct_1('#skF_3'), C_156))=k5_relat_1(k2_funct_1('#skF_3'), C_156) | ~v1_relat_1(C_156) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k6_partfun1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1430, c_1465])).
% 7.27/2.51  tff(c_2041, plain, (![C_172]: (k5_relat_1(k6_partfun1('#skF_2'), k5_relat_1(k2_funct_1('#skF_3'), C_172))=k5_relat_1(k2_funct_1('#skF_3'), C_172) | ~v1_relat_1(C_172))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_1285, c_1492])).
% 7.27/2.51  tff(c_2077, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3')) | ~v1_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_536, c_2041])).
% 7.27/2.51  tff(c_2094, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1285, c_103, c_1430, c_2077])).
% 7.27/2.51  tff(c_2146, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_42, c_2094])).
% 7.27/2.51  tff(c_2164, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_98, c_82, c_2146])).
% 7.27/2.51  tff(c_5426, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5396, c_2164])).
% 7.27/2.51  tff(c_160, plain, (![A_78]: (k5_relat_1(k6_partfun1(k1_relat_1(A_78)), A_78)=A_78 | ~v1_relat_1(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_24])).
% 7.27/2.51  tff(c_169, plain, (![A_19]: (k5_relat_1(k6_partfun1(A_19), k6_partfun1(A_19))=k6_partfun1(A_19) | ~v1_relat_1(k6_partfun1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_160])).
% 7.27/2.51  tff(c_173, plain, (![A_19]: (k5_relat_1(k6_partfun1(A_19), k6_partfun1(A_19))=k6_partfun1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_169])).
% 7.27/2.51  tff(c_46, plain, (![A_31]: (k5_relat_1(k2_funct_1(A_31), A_31)=k6_relat_1(k2_relat_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.27/2.51  tff(c_101, plain, (![A_31]: (k5_relat_1(k2_funct_1(A_31), A_31)=k6_partfun1(k2_relat_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_46])).
% 7.27/2.51  tff(c_2073, plain, (k5_relat_1(k6_partfun1('#skF_2'), k6_partfun1(k2_relat_1('#skF_3')))=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_101, c_2041])).
% 7.27/2.51  tff(c_2092, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_98, c_82, c_158, c_173, c_720, c_2073])).
% 7.27/2.51  tff(c_18, plain, (![A_12, B_16, C_18]: (k5_relat_1(k5_relat_1(A_12, B_16), C_18)=k5_relat_1(A_12, k5_relat_1(B_16, C_18)) | ~v1_relat_1(C_18) | ~v1_relat_1(B_16) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.27/2.51  tff(c_2104, plain, (![C_18]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_18))=k5_relat_1(k6_partfun1('#skF_2'), C_18) | ~v1_relat_1(C_18) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2092, c_18])).
% 7.27/2.51  tff(c_2118, plain, (![C_18]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_18))=k5_relat_1(k6_partfun1('#skF_2'), C_18) | ~v1_relat_1(C_18))), inference(demodulation, [status(thm), theory('equality')], [c_1285, c_158, c_2104])).
% 7.27/2.51  tff(c_4931, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4918, c_2118])).
% 7.27/2.51  tff(c_4951, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_4931])).
% 7.27/2.51  tff(c_6981, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5047, c_5426, c_4951])).
% 7.27/2.51  tff(c_6982, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_6981])).
% 7.27/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.27/2.51  
% 7.27/2.51  Inference rules
% 7.27/2.51  ----------------------
% 7.27/2.51  #Ref     : 0
% 7.27/2.51  #Sup     : 1458
% 7.27/2.51  #Fact    : 0
% 7.27/2.51  #Define  : 0
% 7.27/2.51  #Split   : 9
% 7.27/2.51  #Chain   : 0
% 7.27/2.51  #Close   : 0
% 7.27/2.51  
% 7.27/2.51  Ordering : KBO
% 7.27/2.51  
% 7.27/2.51  Simplification rules
% 7.27/2.51  ----------------------
% 7.27/2.51  #Subsume      : 82
% 7.27/2.51  #Demod        : 2514
% 7.27/2.51  #Tautology    : 782
% 7.27/2.51  #SimpNegUnit  : 2
% 7.27/2.51  #BackRed      : 33
% 7.27/2.51  
% 7.27/2.51  #Partial instantiations: 0
% 7.27/2.51  #Strategies tried      : 1
% 7.27/2.51  
% 7.27/2.51  Timing (in seconds)
% 7.27/2.51  ----------------------
% 7.27/2.51  Preprocessing        : 0.39
% 7.27/2.51  Parsing              : 0.21
% 7.27/2.51  CNF conversion       : 0.03
% 7.27/2.51  Main loop            : 1.32
% 7.27/2.51  Inferencing          : 0.42
% 7.27/2.51  Reduction            : 0.53
% 7.27/2.51  Demodulation         : 0.39
% 7.27/2.51  BG Simplification    : 0.05
% 7.27/2.51  Subsumption          : 0.23
% 7.27/2.51  Abstraction          : 0.06
% 7.27/2.51  MUC search           : 0.00
% 7.27/2.51  Cooper               : 0.00
% 7.27/2.51  Total                : 1.77
% 7.27/2.51  Index Insertion      : 0.00
% 7.27/2.51  Index Deletion       : 0.00
% 7.27/2.51  Index Matching       : 0.00
% 7.27/2.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
