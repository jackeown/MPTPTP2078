%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:55 EST 2020

% Result     : Theorem 6.25s
% Output     : CNFRefutation 6.60s
% Verified   : 
% Statistics : Number of formulae       :  189 (2241 expanded)
%              Number of leaves         :   55 ( 818 expanded)
%              Depth                    :   23
%              Number of atoms          :  389 (7395 expanded)
%              Number of equality atoms :  120 (2425 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_145,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_151,axiom,(
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

tff(f_113,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_155,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_175,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_179,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_163,axiom,(
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

tff(f_111,axiom,(
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

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

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

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_123,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_133,axiom,(
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

tff(c_144,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_156,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_144])).

tff(c_189,plain,(
    ! [C_85,A_86,B_87] :
      ( v4_relat_1(C_85,A_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_201,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_189])).

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

tff(c_155,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_144])).

tff(c_98,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_72,plain,(
    ! [A_59] : k6_relat_1(A_59) = k6_partfun1(A_59) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_38,plain,(
    ! [A_29] : v2_funct_1(k6_relat_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_101,plain,(
    ! [A_29] : v2_funct_1(k6_partfun1(A_29)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_38])).

tff(c_86,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_618,plain,(
    ! [A_124,B_125,C_126] :
      ( k2_relset_1(A_124,B_125,C_126) = k2_relat_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_624,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_618])).

tff(c_631,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_624])).

tff(c_2917,plain,(
    ! [B_212,C_216,A_217,F_213,D_214,E_215] :
      ( m1_subset_1(k1_partfun1(A_217,B_212,C_216,D_214,E_215,F_213),k1_zfmisc_1(k2_zfmisc_1(A_217,D_214)))
      | ~ m1_subset_1(F_213,k1_zfmisc_1(k2_zfmisc_1(C_216,D_214)))
      | ~ v1_funct_1(F_213)
      | ~ m1_subset_1(E_215,k1_zfmisc_1(k2_zfmisc_1(A_217,B_212)))
      | ~ v1_funct_1(E_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_68,plain,(
    ! [A_52] : m1_subset_1(k6_partfun1(A_52),k1_zfmisc_1(k2_zfmisc_1(A_52,A_52))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_84,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_2155,plain,(
    ! [D_173,C_174,A_175,B_176] :
      ( D_173 = C_174
      | ~ r2_relset_1(A_175,B_176,C_174,D_173)
      | ~ m1_subset_1(D_173,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176)))
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2163,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_84,c_2155])).

tff(c_2178,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2163])).

tff(c_2277,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2178])).

tff(c_2925,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2917,c_2277])).

tff(c_2950,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_94,c_92,c_88,c_2925])).

tff(c_2951,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2178])).

tff(c_3175,plain,(
    ! [A_228,F_232,C_227,E_229,B_231,D_230] :
      ( k1_partfun1(A_228,B_231,C_227,D_230,E_229,F_232) = k5_relat_1(E_229,F_232)
      | ~ m1_subset_1(F_232,k1_zfmisc_1(k2_zfmisc_1(C_227,D_230)))
      | ~ v1_funct_1(F_232)
      | ~ m1_subset_1(E_229,k1_zfmisc_1(k2_zfmisc_1(A_228,B_231)))
      | ~ v1_funct_1(E_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_3181,plain,(
    ! [A_228,B_231,E_229] :
      ( k1_partfun1(A_228,B_231,'#skF_2','#skF_1',E_229,'#skF_4') = k5_relat_1(E_229,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_229,k1_zfmisc_1(k2_zfmisc_1(A_228,B_231)))
      | ~ v1_funct_1(E_229) ) ),
    inference(resolution,[status(thm)],[c_88,c_3175])).

tff(c_3528,plain,(
    ! [A_251,B_252,E_253] :
      ( k1_partfun1(A_251,B_252,'#skF_2','#skF_1',E_253,'#skF_4') = k5_relat_1(E_253,'#skF_4')
      | ~ m1_subset_1(E_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252)))
      | ~ v1_funct_1(E_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_3181])).

tff(c_3537,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_3528])).

tff(c_3545,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_2951,c_3537])).

tff(c_34,plain,(
    ! [A_26,B_28] :
      ( v2_funct_1(A_26)
      | k2_relat_1(B_28) != k1_relat_1(A_26)
      | ~ v2_funct_1(k5_relat_1(B_28,A_26))
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3555,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3545,c_34])).

tff(c_3570,plain,
    ( v2_funct_1('#skF_4')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_92,c_155,c_98,c_101,c_631,c_3555])).

tff(c_3578,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3570])).

tff(c_200,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_94,c_189])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k7_relat_1(B_11,A_10) = B_11
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_204,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_200,c_16])).

tff(c_207,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_204])).

tff(c_266,plain,(
    ! [B_95,A_96] :
      ( k2_relat_1(k7_relat_1(B_95,A_96)) = k9_relat_1(B_95,A_96)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_281,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_266])).

tff(c_289,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_281])).

tff(c_633,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_289])).

tff(c_20,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_105,plain,(
    ! [A_19] : k1_relat_1(k6_partfun1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_20])).

tff(c_14,plain,(
    ! [A_7,B_9] :
      ( k10_relat_1(A_7,k1_relat_1(B_9)) = k1_relat_1(k5_relat_1(A_7,B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_896,plain,(
    ! [B_139,A_140] :
      ( k9_relat_1(B_139,k10_relat_1(B_139,A_140)) = A_140
      | ~ r1_tarski(A_140,k2_relat_1(B_139))
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_898,plain,(
    ! [A_140] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_140)) = A_140
      | ~ r1_tarski(A_140,'#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_631,c_896])).

tff(c_917,plain,(
    ! [A_141] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_141)) = A_141
      | ~ r1_tarski(A_141,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_98,c_898])).

tff(c_934,plain,(
    ! [B_9] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_9))) = k1_relat_1(B_9)
      | ~ r1_tarski(k1_relat_1(B_9),'#skF_2')
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_917])).

tff(c_942,plain,(
    ! [B_9] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_9))) = k1_relat_1(B_9)
      | ~ r1_tarski(k1_relat_1(B_9),'#skF_2')
      | ~ v1_relat_1(B_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_934])).

tff(c_3564,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3545,c_942])).

tff(c_3576,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_633,c_105,c_3564])).

tff(c_3579,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_3578,c_3576])).

tff(c_3582,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_3579])).

tff(c_3586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_201,c_3582])).

tff(c_3588,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3570])).

tff(c_24,plain,(
    ! [A_20] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_20)),A_20) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_103,plain,(
    ! [A_20] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_20)),A_20) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_24])).

tff(c_3652,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3588,c_103])).

tff(c_3672,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_3652])).

tff(c_154,plain,(
    ! [A_52] : v1_relat_1(k6_partfun1(A_52)) ),
    inference(resolution,[status(thm)],[c_68,c_144])).

tff(c_1284,plain,(
    ! [A_152,B_153,C_154] :
      ( k5_relat_1(k5_relat_1(A_152,B_153),C_154) = k5_relat_1(A_152,k5_relat_1(B_153,C_154))
      | ~ v1_relat_1(C_154)
      | ~ v1_relat_1(B_153)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1340,plain,(
    ! [A_20,C_154] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_20)),k5_relat_1(A_20,C_154)) = k5_relat_1(A_20,C_154)
      | ~ v1_relat_1(C_154)
      | ~ v1_relat_1(A_20)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_20)))
      | ~ v1_relat_1(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_1284])).

tff(c_3905,plain,(
    ! [A_264,C_265] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_264)),k5_relat_1(A_264,C_265)) = k5_relat_1(A_264,C_265)
      | ~ v1_relat_1(C_265)
      | ~ v1_relat_1(A_264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_1340])).

tff(c_3950,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_1')) = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3545,c_3905])).

tff(c_4049,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_1')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_156,c_3545,c_3950])).

tff(c_22,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_104,plain,(
    ! [A_19] : k2_relat_1(k6_partfun1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_22])).

tff(c_26,plain,(
    ! [B_22,A_21] :
      ( k5_relat_1(B_22,k6_relat_1(A_21)) = B_22
      | ~ r1_tarski(k2_relat_1(B_22),A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_480,plain,(
    ! [B_113,A_114] :
      ( k5_relat_1(B_113,k6_partfun1(A_114)) = B_113
      | ~ r1_tarski(k2_relat_1(B_113),A_114)
      | ~ v1_relat_1(B_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_26])).

tff(c_486,plain,(
    ! [A_19,A_114] :
      ( k5_relat_1(k6_partfun1(A_19),k6_partfun1(A_114)) = k6_partfun1(A_19)
      | ~ r1_tarski(A_19,A_114)
      | ~ v1_relat_1(k6_partfun1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_480])).

tff(c_492,plain,(
    ! [A_19,A_114] :
      ( k5_relat_1(k6_partfun1(A_19),k6_partfun1(A_114)) = k6_partfun1(A_19)
      | ~ r1_tarski(A_19,A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_486])).

tff(c_648,plain,(
    ! [A_127,B_128] :
      ( k10_relat_1(A_127,k1_relat_1(B_128)) = k1_relat_1(k5_relat_1(A_127,B_128))
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_660,plain,(
    ! [A_127,A_19] :
      ( k1_relat_1(k5_relat_1(A_127,k6_partfun1(A_19))) = k10_relat_1(A_127,A_19)
      | ~ v1_relat_1(k6_partfun1(A_19))
      | ~ v1_relat_1(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_648])).

tff(c_721,plain,(
    ! [A_131,A_132] :
      ( k1_relat_1(k5_relat_1(A_131,k6_partfun1(A_132))) = k10_relat_1(A_131,A_132)
      | ~ v1_relat_1(A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_660])).

tff(c_757,plain,(
    ! [A_19,A_114] :
      ( k10_relat_1(k6_partfun1(A_19),A_114) = k1_relat_1(k6_partfun1(A_19))
      | ~ v1_relat_1(k6_partfun1(A_19))
      | ~ r1_tarski(A_19,A_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_721])).

tff(c_818,plain,(
    ! [A_135,A_136] :
      ( k10_relat_1(k6_partfun1(A_135),A_136) = A_135
      | ~ r1_tarski(A_135,A_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_105,c_757])).

tff(c_829,plain,(
    ! [A_135,B_9] :
      ( k1_relat_1(k5_relat_1(k6_partfun1(A_135),B_9)) = A_135
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(k6_partfun1(A_135))
      | ~ r1_tarski(A_135,k1_relat_1(B_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_14])).

tff(c_845,plain,(
    ! [A_135,B_9] :
      ( k1_relat_1(k5_relat_1(k6_partfun1(A_135),B_9)) = A_135
      | ~ v1_relat_1(B_9)
      | ~ r1_tarski(A_135,k1_relat_1(B_9)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_829])).

tff(c_4172,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1(k6_partfun1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(k6_partfun1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4049,c_845])).

tff(c_4198,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_154,c_105,c_4172])).

tff(c_4236,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4198])).

tff(c_4239,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_4236])).

tff(c_4243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_200,c_4239])).

tff(c_4244,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4198])).

tff(c_82,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_40,plain,(
    ! [A_30] :
      ( k2_relat_1(k2_funct_1(A_30)) = k1_relat_1(A_30)
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_30,plain,(
    ! [A_23] :
      ( v1_relat_1(k2_funct_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_493,plain,(
    ! [B_113] :
      ( k5_relat_1(B_113,k6_partfun1(k2_relat_1(B_113))) = B_113
      | ~ v1_relat_1(B_113) ) ),
    inference(resolution,[status(thm)],[c_6,c_480])).

tff(c_760,plain,(
    ! [B_113] :
      ( k10_relat_1(B_113,k2_relat_1(B_113)) = k1_relat_1(B_113)
      | ~ v1_relat_1(B_113)
      | ~ v1_relat_1(B_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_721])).

tff(c_927,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_760,c_917])).

tff(c_938,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_155,c_6,c_631,c_631,c_927])).

tff(c_46,plain,(
    ! [A_31] :
      ( k5_relat_1(A_31,k2_funct_1(A_31)) = k6_relat_1(k1_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_99,plain,(
    ! [A_31] :
      ( k5_relat_1(A_31,k2_funct_1(A_31)) = k6_partfun1(k1_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_46])).

tff(c_1148,plain,(
    ! [B_149] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_149))) = k1_relat_1(B_149)
      | ~ r1_tarski(k1_relat_1(B_149),'#skF_2')
      | ~ v1_relat_1(B_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_934])).

tff(c_1158,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_1148])).

tff(c_1176,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_98,c_82,c_938,c_105,c_1158])).

tff(c_1274,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1176])).

tff(c_1277,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1274])).

tff(c_1281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_98,c_1277])).

tff(c_1283,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1176])).

tff(c_42,plain,(
    ! [A_30] :
      ( k1_relat_1(k2_funct_1(A_30)) = k2_relat_1(A_30)
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1282,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1176])).

tff(c_1361,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1282])).

tff(c_1364,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1361])).

tff(c_1370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_98,c_82,c_6,c_631,c_1364])).

tff(c_1371,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1282])).

tff(c_1403,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1371,c_103])).

tff(c_1428,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1283,c_1403])).

tff(c_18,plain,(
    ! [A_12,B_16,C_18] :
      ( k5_relat_1(k5_relat_1(A_12,B_16),C_18) = k5_relat_1(A_12,k5_relat_1(B_16,C_18))
      | ~ v1_relat_1(C_18)
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1610,plain,(
    ! [C_18] :
      ( k5_relat_1(k6_partfun1('#skF_2'),k5_relat_1(k2_funct_1('#skF_3'),C_18)) = k5_relat_1(k2_funct_1('#skF_3'),C_18)
      | ~ v1_relat_1(C_18)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k6_partfun1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1428,c_18])).

tff(c_2181,plain,(
    ! [C_177] :
      ( k5_relat_1(k6_partfun1('#skF_2'),k5_relat_1(k2_funct_1('#skF_3'),C_177)) = k5_relat_1(k2_funct_1('#skF_3'),C_177)
      | ~ v1_relat_1(C_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_1283,c_1610])).

tff(c_2223,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_2181])).

tff(c_2242,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1283,c_154,c_1428,c_2223])).

tff(c_2981,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2242])).

tff(c_3001,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_98,c_82,c_2981])).

tff(c_4256,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4244,c_3001])).

tff(c_165,plain,(
    ! [A_81] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_81)),A_81) = A_81
      | ~ v1_relat_1(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_24])).

tff(c_174,plain,(
    ! [A_19] :
      ( k5_relat_1(k6_partfun1(A_19),k6_partfun1(A_19)) = k6_partfun1(A_19)
      | ~ v1_relat_1(k6_partfun1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_165])).

tff(c_178,plain,(
    ! [A_19] : k5_relat_1(k6_partfun1(A_19),k6_partfun1(A_19)) = k6_partfun1(A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_174])).

tff(c_44,plain,(
    ! [A_31] :
      ( k5_relat_1(k2_funct_1(A_31),A_31) = k6_relat_1(k2_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_100,plain,(
    ! [A_31] :
      ( k5_relat_1(k2_funct_1(A_31),A_31) = k6_partfun1(k2_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_44])).

tff(c_2215,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k6_partfun1(k2_relat_1('#skF_3'))) = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_2181])).

tff(c_2238,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_98,c_82,c_155,c_178,c_631,c_2215])).

tff(c_2255,plain,(
    ! [C_18] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_18)) = k5_relat_1(k6_partfun1('#skF_2'),C_18)
      | ~ v1_relat_1(C_18)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2238,c_18])).

tff(c_2271,plain,(
    ! [C_18] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_18)) = k5_relat_1(k6_partfun1('#skF_2'),C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1283,c_155,c_2255])).

tff(c_3552,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3545,c_2271])).

tff(c_3568,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_3552])).

tff(c_5815,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3672,c_4256,c_3568])).

tff(c_5816,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_5815])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.30  % Computer   : n004.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % DateTime   : Tue Dec  1 10:27:38 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.16/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.25/2.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.25/2.29  
% 6.25/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.25/2.29  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.25/2.29  
% 6.25/2.29  %Foreground sorts:
% 6.25/2.29  
% 6.25/2.29  
% 6.25/2.29  %Background operators:
% 6.25/2.29  
% 6.25/2.29  
% 6.25/2.29  %Foreground operators:
% 6.25/2.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.25/2.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.25/2.29  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.25/2.29  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.25/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.25/2.29  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.25/2.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.25/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.25/2.29  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.25/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.25/2.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.25/2.29  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.25/2.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.25/2.29  tff('#skF_2', type, '#skF_2': $i).
% 6.25/2.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.25/2.29  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.25/2.29  tff('#skF_3', type, '#skF_3': $i).
% 6.25/2.29  tff('#skF_1', type, '#skF_1': $i).
% 6.25/2.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.25/2.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.25/2.29  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.25/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.25/2.29  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.25/2.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.25/2.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.25/2.29  tff('#skF_4', type, '#skF_4': $i).
% 6.25/2.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.25/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.25/2.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.25/2.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.25/2.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.25/2.29  
% 6.60/2.34  tff(f_234, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 6.60/2.34  tff(f_145, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.60/2.34  tff(f_151, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.60/2.34  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 6.60/2.34  tff(f_191, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.60/2.34  tff(f_113, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 6.60/2.34  tff(f_155, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.60/2.34  tff(f_175, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.60/2.34  tff(f_179, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.60/2.34  tff(f_163, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.60/2.34  tff(f_189, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.60/2.34  tff(f_111, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 6.60/2.34  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 6.60/2.34  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 6.60/2.34  tff(f_68, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.60/2.34  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 6.60/2.34  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 6.60/2.34  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 6.60/2.34  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 6.60/2.34  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 6.60/2.34  tff(f_123, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 6.60/2.34  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.60/2.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.60/2.34  tff(f_133, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 6.60/2.34  tff(c_76, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_234])).
% 6.60/2.34  tff(c_88, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_234])).
% 6.60/2.34  tff(c_144, plain, (![C_75, A_76, B_77]: (v1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.60/2.34  tff(c_156, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_88, c_144])).
% 6.60/2.34  tff(c_189, plain, (![C_85, A_86, B_87]: (v4_relat_1(C_85, A_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 6.60/2.34  tff(c_201, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_88, c_189])).
% 6.60/2.34  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k1_relat_1(B_4), A_3) | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.60/2.34  tff(c_92, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_234])).
% 6.60/2.34  tff(c_94, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_234])).
% 6.60/2.34  tff(c_155, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_144])).
% 6.60/2.34  tff(c_98, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_234])).
% 6.60/2.34  tff(c_72, plain, (![A_59]: (k6_relat_1(A_59)=k6_partfun1(A_59))), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.60/2.34  tff(c_38, plain, (![A_29]: (v2_funct_1(k6_relat_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.60/2.34  tff(c_101, plain, (![A_29]: (v2_funct_1(k6_partfun1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_38])).
% 6.60/2.34  tff(c_86, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_234])).
% 6.60/2.34  tff(c_618, plain, (![A_124, B_125, C_126]: (k2_relset_1(A_124, B_125, C_126)=k2_relat_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.60/2.34  tff(c_624, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_618])).
% 6.60/2.34  tff(c_631, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_624])).
% 6.60/2.34  tff(c_2917, plain, (![B_212, C_216, A_217, F_213, D_214, E_215]: (m1_subset_1(k1_partfun1(A_217, B_212, C_216, D_214, E_215, F_213), k1_zfmisc_1(k2_zfmisc_1(A_217, D_214))) | ~m1_subset_1(F_213, k1_zfmisc_1(k2_zfmisc_1(C_216, D_214))) | ~v1_funct_1(F_213) | ~m1_subset_1(E_215, k1_zfmisc_1(k2_zfmisc_1(A_217, B_212))) | ~v1_funct_1(E_215))), inference(cnfTransformation, [status(thm)], [f_175])).
% 6.60/2.34  tff(c_68, plain, (![A_52]: (m1_subset_1(k6_partfun1(A_52), k1_zfmisc_1(k2_zfmisc_1(A_52, A_52))))), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.60/2.34  tff(c_84, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_234])).
% 6.60/2.34  tff(c_2155, plain, (![D_173, C_174, A_175, B_176]: (D_173=C_174 | ~r2_relset_1(A_175, B_176, C_174, D_173) | ~m1_subset_1(D_173, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.60/2.34  tff(c_2163, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_84, c_2155])).
% 6.60/2.34  tff(c_2178, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2163])).
% 6.60/2.34  tff(c_2277, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2178])).
% 6.60/2.34  tff(c_2925, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2917, c_2277])).
% 6.60/2.34  tff(c_2950, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_94, c_92, c_88, c_2925])).
% 6.60/2.34  tff(c_2951, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2178])).
% 6.60/2.34  tff(c_3175, plain, (![A_228, F_232, C_227, E_229, B_231, D_230]: (k1_partfun1(A_228, B_231, C_227, D_230, E_229, F_232)=k5_relat_1(E_229, F_232) | ~m1_subset_1(F_232, k1_zfmisc_1(k2_zfmisc_1(C_227, D_230))) | ~v1_funct_1(F_232) | ~m1_subset_1(E_229, k1_zfmisc_1(k2_zfmisc_1(A_228, B_231))) | ~v1_funct_1(E_229))), inference(cnfTransformation, [status(thm)], [f_189])).
% 6.60/2.34  tff(c_3181, plain, (![A_228, B_231, E_229]: (k1_partfun1(A_228, B_231, '#skF_2', '#skF_1', E_229, '#skF_4')=k5_relat_1(E_229, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_229, k1_zfmisc_1(k2_zfmisc_1(A_228, B_231))) | ~v1_funct_1(E_229))), inference(resolution, [status(thm)], [c_88, c_3175])).
% 6.60/2.34  tff(c_3528, plain, (![A_251, B_252, E_253]: (k1_partfun1(A_251, B_252, '#skF_2', '#skF_1', E_253, '#skF_4')=k5_relat_1(E_253, '#skF_4') | ~m1_subset_1(E_253, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))) | ~v1_funct_1(E_253))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_3181])).
% 6.60/2.34  tff(c_3537, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_3528])).
% 6.60/2.34  tff(c_3545, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_2951, c_3537])).
% 6.60/2.34  tff(c_34, plain, (![A_26, B_28]: (v2_funct_1(A_26) | k2_relat_1(B_28)!=k1_relat_1(A_26) | ~v2_funct_1(k5_relat_1(B_28, A_26)) | ~v1_funct_1(B_28) | ~v1_relat_1(B_28) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.60/2.34  tff(c_3555, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3545, c_34])).
% 6.60/2.34  tff(c_3570, plain, (v2_funct_1('#skF_4') | k1_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_156, c_92, c_155, c_98, c_101, c_631, c_3555])).
% 6.60/2.34  tff(c_3578, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_3570])).
% 6.60/2.34  tff(c_200, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_94, c_189])).
% 6.60/2.34  tff(c_16, plain, (![B_11, A_10]: (k7_relat_1(B_11, A_10)=B_11 | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.60/2.34  tff(c_204, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_200, c_16])).
% 6.60/2.34  tff(c_207, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_204])).
% 6.60/2.34  tff(c_266, plain, (![B_95, A_96]: (k2_relat_1(k7_relat_1(B_95, A_96))=k9_relat_1(B_95, A_96) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.60/2.34  tff(c_281, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_207, c_266])).
% 6.60/2.34  tff(c_289, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_281])).
% 6.60/2.34  tff(c_633, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_631, c_289])).
% 6.60/2.34  tff(c_20, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.60/2.34  tff(c_105, plain, (![A_19]: (k1_relat_1(k6_partfun1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_20])).
% 6.60/2.34  tff(c_14, plain, (![A_7, B_9]: (k10_relat_1(A_7, k1_relat_1(B_9))=k1_relat_1(k5_relat_1(A_7, B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.60/2.34  tff(c_896, plain, (![B_139, A_140]: (k9_relat_1(B_139, k10_relat_1(B_139, A_140))=A_140 | ~r1_tarski(A_140, k2_relat_1(B_139)) | ~v1_funct_1(B_139) | ~v1_relat_1(B_139))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.60/2.34  tff(c_898, plain, (![A_140]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_140))=A_140 | ~r1_tarski(A_140, '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_631, c_896])).
% 6.60/2.34  tff(c_917, plain, (![A_141]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_141))=A_141 | ~r1_tarski(A_141, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_98, c_898])).
% 6.60/2.34  tff(c_934, plain, (![B_9]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_9)))=k1_relat_1(B_9) | ~r1_tarski(k1_relat_1(B_9), '#skF_2') | ~v1_relat_1(B_9) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_917])).
% 6.60/2.34  tff(c_942, plain, (![B_9]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_9)))=k1_relat_1(B_9) | ~r1_tarski(k1_relat_1(B_9), '#skF_2') | ~v1_relat_1(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_934])).
% 6.60/2.34  tff(c_3564, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1')))=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3545, c_942])).
% 6.60/2.34  tff(c_3576, plain, (k1_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_633, c_105, c_3564])).
% 6.60/2.34  tff(c_3579, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_3578, c_3576])).
% 6.60/2.34  tff(c_3582, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_3579])).
% 6.60/2.34  tff(c_3586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156, c_201, c_3582])).
% 6.60/2.34  tff(c_3588, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_3570])).
% 6.60/2.34  tff(c_24, plain, (![A_20]: (k5_relat_1(k6_relat_1(k1_relat_1(A_20)), A_20)=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.60/2.34  tff(c_103, plain, (![A_20]: (k5_relat_1(k6_partfun1(k1_relat_1(A_20)), A_20)=A_20 | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_24])).
% 6.60/2.34  tff(c_3652, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3588, c_103])).
% 6.60/2.34  tff(c_3672, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_156, c_3652])).
% 6.60/2.34  tff(c_154, plain, (![A_52]: (v1_relat_1(k6_partfun1(A_52)))), inference(resolution, [status(thm)], [c_68, c_144])).
% 6.60/2.34  tff(c_1284, plain, (![A_152, B_153, C_154]: (k5_relat_1(k5_relat_1(A_152, B_153), C_154)=k5_relat_1(A_152, k5_relat_1(B_153, C_154)) | ~v1_relat_1(C_154) | ~v1_relat_1(B_153) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.60/2.34  tff(c_1340, plain, (![A_20, C_154]: (k5_relat_1(k6_partfun1(k1_relat_1(A_20)), k5_relat_1(A_20, C_154))=k5_relat_1(A_20, C_154) | ~v1_relat_1(C_154) | ~v1_relat_1(A_20) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_20))) | ~v1_relat_1(A_20))), inference(superposition, [status(thm), theory('equality')], [c_103, c_1284])).
% 6.60/2.34  tff(c_3905, plain, (![A_264, C_265]: (k5_relat_1(k6_partfun1(k1_relat_1(A_264)), k5_relat_1(A_264, C_265))=k5_relat_1(A_264, C_265) | ~v1_relat_1(C_265) | ~v1_relat_1(A_264))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_1340])).
% 6.60/2.34  tff(c_3950, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_1'))=k5_relat_1('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3545, c_3905])).
% 6.60/2.34  tff(c_4049, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_1'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_156, c_3545, c_3950])).
% 6.60/2.34  tff(c_22, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.60/2.34  tff(c_104, plain, (![A_19]: (k2_relat_1(k6_partfun1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_22])).
% 6.60/2.34  tff(c_26, plain, (![B_22, A_21]: (k5_relat_1(B_22, k6_relat_1(A_21))=B_22 | ~r1_tarski(k2_relat_1(B_22), A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.60/2.34  tff(c_480, plain, (![B_113, A_114]: (k5_relat_1(B_113, k6_partfun1(A_114))=B_113 | ~r1_tarski(k2_relat_1(B_113), A_114) | ~v1_relat_1(B_113))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_26])).
% 6.60/2.34  tff(c_486, plain, (![A_19, A_114]: (k5_relat_1(k6_partfun1(A_19), k6_partfun1(A_114))=k6_partfun1(A_19) | ~r1_tarski(A_19, A_114) | ~v1_relat_1(k6_partfun1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_480])).
% 6.60/2.34  tff(c_492, plain, (![A_19, A_114]: (k5_relat_1(k6_partfun1(A_19), k6_partfun1(A_114))=k6_partfun1(A_19) | ~r1_tarski(A_19, A_114))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_486])).
% 6.60/2.34  tff(c_648, plain, (![A_127, B_128]: (k10_relat_1(A_127, k1_relat_1(B_128))=k1_relat_1(k5_relat_1(A_127, B_128)) | ~v1_relat_1(B_128) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.60/2.34  tff(c_660, plain, (![A_127, A_19]: (k1_relat_1(k5_relat_1(A_127, k6_partfun1(A_19)))=k10_relat_1(A_127, A_19) | ~v1_relat_1(k6_partfun1(A_19)) | ~v1_relat_1(A_127))), inference(superposition, [status(thm), theory('equality')], [c_105, c_648])).
% 6.60/2.34  tff(c_721, plain, (![A_131, A_132]: (k1_relat_1(k5_relat_1(A_131, k6_partfun1(A_132)))=k10_relat_1(A_131, A_132) | ~v1_relat_1(A_131))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_660])).
% 6.60/2.34  tff(c_757, plain, (![A_19, A_114]: (k10_relat_1(k6_partfun1(A_19), A_114)=k1_relat_1(k6_partfun1(A_19)) | ~v1_relat_1(k6_partfun1(A_19)) | ~r1_tarski(A_19, A_114))), inference(superposition, [status(thm), theory('equality')], [c_492, c_721])).
% 6.60/2.34  tff(c_818, plain, (![A_135, A_136]: (k10_relat_1(k6_partfun1(A_135), A_136)=A_135 | ~r1_tarski(A_135, A_136))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_105, c_757])).
% 6.60/2.34  tff(c_829, plain, (![A_135, B_9]: (k1_relat_1(k5_relat_1(k6_partfun1(A_135), B_9))=A_135 | ~v1_relat_1(B_9) | ~v1_relat_1(k6_partfun1(A_135)) | ~r1_tarski(A_135, k1_relat_1(B_9)))), inference(superposition, [status(thm), theory('equality')], [c_818, c_14])).
% 6.60/2.34  tff(c_845, plain, (![A_135, B_9]: (k1_relat_1(k5_relat_1(k6_partfun1(A_135), B_9))=A_135 | ~v1_relat_1(B_9) | ~r1_tarski(A_135, k1_relat_1(B_9)))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_829])).
% 6.60/2.34  tff(c_4172, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v1_relat_1(k6_partfun1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(k6_partfun1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4049, c_845])).
% 6.60/2.34  tff(c_4198, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_154, c_105, c_4172])).
% 6.60/2.34  tff(c_4236, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_4198])).
% 6.60/2.34  tff(c_4239, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_4236])).
% 6.60/2.34  tff(c_4243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_200, c_4239])).
% 6.60/2.34  tff(c_4244, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_4198])).
% 6.60/2.34  tff(c_82, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_234])).
% 6.60/2.34  tff(c_40, plain, (![A_30]: (k2_relat_1(k2_funct_1(A_30))=k1_relat_1(A_30) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.60/2.34  tff(c_30, plain, (![A_23]: (v1_relat_1(k2_funct_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.60/2.34  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.60/2.34  tff(c_493, plain, (![B_113]: (k5_relat_1(B_113, k6_partfun1(k2_relat_1(B_113)))=B_113 | ~v1_relat_1(B_113))), inference(resolution, [status(thm)], [c_6, c_480])).
% 6.60/2.34  tff(c_760, plain, (![B_113]: (k10_relat_1(B_113, k2_relat_1(B_113))=k1_relat_1(B_113) | ~v1_relat_1(B_113) | ~v1_relat_1(B_113))), inference(superposition, [status(thm), theory('equality')], [c_493, c_721])).
% 6.60/2.34  tff(c_927, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_760, c_917])).
% 6.60/2.34  tff(c_938, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_155, c_6, c_631, c_631, c_927])).
% 6.60/2.34  tff(c_46, plain, (![A_31]: (k5_relat_1(A_31, k2_funct_1(A_31))=k6_relat_1(k1_relat_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.60/2.34  tff(c_99, plain, (![A_31]: (k5_relat_1(A_31, k2_funct_1(A_31))=k6_partfun1(k1_relat_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_46])).
% 6.60/2.34  tff(c_1148, plain, (![B_149]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_149)))=k1_relat_1(B_149) | ~r1_tarski(k1_relat_1(B_149), '#skF_2') | ~v1_relat_1(B_149))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_934])).
% 6.60/2.34  tff(c_1158, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))))=k1_relat_1(k2_funct_1('#skF_3')) | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_99, c_1148])).
% 6.60/2.34  tff(c_1176, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_98, c_82, c_938, c_105, c_1158])).
% 6.60/2.34  tff(c_1274, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1176])).
% 6.60/2.34  tff(c_1277, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_1274])).
% 6.60/2.34  tff(c_1281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_98, c_1277])).
% 6.60/2.34  tff(c_1283, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1176])).
% 6.60/2.34  tff(c_42, plain, (![A_30]: (k1_relat_1(k2_funct_1(A_30))=k2_relat_1(A_30) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.60/2.34  tff(c_1282, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_1176])).
% 6.60/2.34  tff(c_1361, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_1282])).
% 6.60/2.34  tff(c_1364, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_42, c_1361])).
% 6.60/2.34  tff(c_1370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_98, c_82, c_6, c_631, c_1364])).
% 6.60/2.34  tff(c_1371, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_1282])).
% 6.60/2.34  tff(c_1403, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1371, c_103])).
% 6.60/2.34  tff(c_1428, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1283, c_1403])).
% 6.60/2.34  tff(c_18, plain, (![A_12, B_16, C_18]: (k5_relat_1(k5_relat_1(A_12, B_16), C_18)=k5_relat_1(A_12, k5_relat_1(B_16, C_18)) | ~v1_relat_1(C_18) | ~v1_relat_1(B_16) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.60/2.34  tff(c_1610, plain, (![C_18]: (k5_relat_1(k6_partfun1('#skF_2'), k5_relat_1(k2_funct_1('#skF_3'), C_18))=k5_relat_1(k2_funct_1('#skF_3'), C_18) | ~v1_relat_1(C_18) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k6_partfun1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1428, c_18])).
% 6.60/2.34  tff(c_2181, plain, (![C_177]: (k5_relat_1(k6_partfun1('#skF_2'), k5_relat_1(k2_funct_1('#skF_3'), C_177))=k5_relat_1(k2_funct_1('#skF_3'), C_177) | ~v1_relat_1(C_177))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_1283, c_1610])).
% 6.60/2.34  tff(c_2223, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3')) | ~v1_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_493, c_2181])).
% 6.60/2.34  tff(c_2242, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1283, c_154, c_1428, c_2223])).
% 6.60/2.34  tff(c_2981, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_2242])).
% 6.60/2.34  tff(c_3001, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_98, c_82, c_2981])).
% 6.60/2.34  tff(c_4256, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4244, c_3001])).
% 6.60/2.34  tff(c_165, plain, (![A_81]: (k5_relat_1(k6_partfun1(k1_relat_1(A_81)), A_81)=A_81 | ~v1_relat_1(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_24])).
% 6.60/2.34  tff(c_174, plain, (![A_19]: (k5_relat_1(k6_partfun1(A_19), k6_partfun1(A_19))=k6_partfun1(A_19) | ~v1_relat_1(k6_partfun1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_105, c_165])).
% 6.60/2.34  tff(c_178, plain, (![A_19]: (k5_relat_1(k6_partfun1(A_19), k6_partfun1(A_19))=k6_partfun1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_174])).
% 6.60/2.34  tff(c_44, plain, (![A_31]: (k5_relat_1(k2_funct_1(A_31), A_31)=k6_relat_1(k2_relat_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.60/2.34  tff(c_100, plain, (![A_31]: (k5_relat_1(k2_funct_1(A_31), A_31)=k6_partfun1(k2_relat_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_44])).
% 6.60/2.34  tff(c_2215, plain, (k5_relat_1(k6_partfun1('#skF_2'), k6_partfun1(k2_relat_1('#skF_3')))=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_100, c_2181])).
% 6.60/2.34  tff(c_2238, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_98, c_82, c_155, c_178, c_631, c_2215])).
% 6.60/2.34  tff(c_2255, plain, (![C_18]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_18))=k5_relat_1(k6_partfun1('#skF_2'), C_18) | ~v1_relat_1(C_18) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2238, c_18])).
% 6.60/2.34  tff(c_2271, plain, (![C_18]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_18))=k5_relat_1(k6_partfun1('#skF_2'), C_18) | ~v1_relat_1(C_18))), inference(demodulation, [status(thm), theory('equality')], [c_1283, c_155, c_2255])).
% 6.60/2.34  tff(c_3552, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3545, c_2271])).
% 6.60/2.34  tff(c_3568, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_3552])).
% 6.60/2.34  tff(c_5815, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3672, c_4256, c_3568])).
% 6.60/2.34  tff(c_5816, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_5815])).
% 6.60/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.60/2.34  
% 6.60/2.34  Inference rules
% 6.60/2.34  ----------------------
% 6.60/2.34  #Ref     : 0
% 6.60/2.34  #Sup     : 1213
% 6.60/2.34  #Fact    : 0
% 6.60/2.34  #Define  : 0
% 6.60/2.34  #Split   : 11
% 6.60/2.34  #Chain   : 0
% 6.60/2.34  #Close   : 0
% 6.60/2.34  
% 6.60/2.34  Ordering : KBO
% 6.60/2.34  
% 6.60/2.34  Simplification rules
% 6.60/2.34  ----------------------
% 6.60/2.34  #Subsume      : 51
% 6.60/2.34  #Demod        : 2029
% 6.60/2.34  #Tautology    : 670
% 6.60/2.34  #SimpNegUnit  : 2
% 6.60/2.34  #BackRed      : 31
% 6.60/2.34  
% 6.60/2.34  #Partial instantiations: 0
% 6.60/2.34  #Strategies tried      : 1
% 6.60/2.34  
% 6.60/2.34  Timing (in seconds)
% 6.60/2.34  ----------------------
% 6.60/2.35  Preprocessing        : 0.39
% 6.60/2.35  Parsing              : 0.21
% 6.60/2.35  CNF conversion       : 0.03
% 6.60/2.35  Main loop            : 1.16
% 6.60/2.35  Inferencing          : 0.37
% 6.60/2.35  Reduction            : 0.44
% 6.60/2.35  Demodulation         : 0.34
% 6.60/2.35  BG Simplification    : 0.05
% 6.60/2.35  Subsumption          : 0.22
% 6.60/2.35  Abstraction          : 0.05
% 6.60/2.35  MUC search           : 0.00
% 6.60/2.35  Cooper               : 0.00
% 6.60/2.35  Total                : 1.64
% 6.60/2.35  Index Insertion      : 0.00
% 6.60/2.35  Index Deletion       : 0.00
% 6.60/2.35  Index Matching       : 0.00
% 6.60/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
