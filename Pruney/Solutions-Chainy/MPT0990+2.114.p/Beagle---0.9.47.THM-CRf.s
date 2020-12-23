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
% DateTime   : Thu Dec  3 10:13:12 EST 2020

% Result     : Theorem 9.44s
% Output     : CNFRefutation 9.44s
% Verified   : 
% Statistics : Number of formulae       :  164 (1234 expanded)
%              Number of leaves         :   50 ( 453 expanded)
%              Depth                    :   20
%              Number of atoms          :  370 (3931 expanded)
%              Number of equality atoms :   93 (1042 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_206,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_136,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_116,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_170,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_146,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_126,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_158,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_144,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_168,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(c_68,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_115,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_124,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_115])).

tff(c_133,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_124])).

tff(c_164,plain,(
    ! [C_73,A_74,B_75] :
      ( v4_relat_1(C_73,A_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_176,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_164])).

tff(c_86,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_121,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_86,c_115])).

tff(c_130,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_121])).

tff(c_175,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_164])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_90,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_74,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_26,plain,(
    ! [A_22] :
      ( v1_relat_1(k2_funct_1(A_22))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_78,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_317,plain,(
    ! [A_97,B_98,C_99] :
      ( k2_relset_1(A_97,B_98,C_99) = k2_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_323,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_317])).

tff(c_329,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_323])).

tff(c_244,plain,(
    ! [A_90] :
      ( k1_relat_1(k2_funct_1(A_90)) = k2_relat_1(A_90)
      | ~ v2_funct_1(A_90)
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_183,plain,(
    ! [B_80,A_81] :
      ( v4_relat_1(B_80,A_81)
      | ~ r1_tarski(k1_relat_1(B_80),A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_192,plain,(
    ! [B_80] :
      ( v4_relat_1(B_80,k1_relat_1(B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_6,c_183])).

tff(c_644,plain,(
    ! [A_118] :
      ( v4_relat_1(k2_funct_1(A_118),k2_relat_1(A_118))
      | ~ v1_relat_1(k2_funct_1(A_118))
      | ~ v2_funct_1(A_118)
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_192])).

tff(c_647,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_644])).

tff(c_652,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_90,c_74,c_647])).

tff(c_653,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_652])).

tff(c_656,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_653])).

tff(c_660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_90,c_656])).

tff(c_662,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_652])).

tff(c_60,plain,(
    ! [A_54] : k6_relat_1(A_54) = k6_partfun1(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_52,plain,(
    ! [A_41] : m1_subset_1(k6_relat_1(A_41),k1_zfmisc_1(k2_zfmisc_1(A_41,A_41))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_91,plain,(
    ! [A_41] : m1_subset_1(k6_partfun1(A_41),k1_zfmisc_1(k2_zfmisc_1(A_41,A_41))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52])).

tff(c_118,plain,(
    ! [A_41] :
      ( v1_relat_1(k6_partfun1(A_41))
      | ~ v1_relat_1(k2_zfmisc_1(A_41,A_41)) ) ),
    inference(resolution,[status(thm)],[c_91,c_115])).

tff(c_127,plain,(
    ! [A_41] : v1_relat_1(k6_partfun1(A_41)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_118])).

tff(c_174,plain,(
    ! [A_41] : v4_relat_1(k6_partfun1(A_41),A_41) ),
    inference(resolution,[status(thm)],[c_91,c_164])).

tff(c_40,plain,(
    ! [A_30] :
      ( k5_relat_1(A_30,k2_funct_1(A_30)) = k6_relat_1(k1_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_92,plain,(
    ! [A_30] :
      ( k5_relat_1(A_30,k2_funct_1(A_30)) = k6_partfun1(k1_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_40])).

tff(c_22,plain,(
    ! [B_21,A_20] :
      ( k5_relat_1(B_21,k6_relat_1(A_20)) = B_21
      | ~ r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_274,plain,(
    ! [B_91,A_92] :
      ( k5_relat_1(B_91,k6_partfun1(A_92)) = B_91
      | ~ r1_tarski(k2_relat_1(B_91),A_92)
      | ~ v1_relat_1(B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_22])).

tff(c_282,plain,(
    ! [B_91] :
      ( k5_relat_1(B_91,k6_partfun1(k2_relat_1(B_91))) = B_91
      | ~ v1_relat_1(B_91) ) ),
    inference(resolution,[status(thm)],[c_6,c_274])).

tff(c_334,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_282])).

tff(c_344,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_334])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( k5_relat_1(k6_relat_1(A_18),B_19) = B_19
      | ~ r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_195,plain,(
    ! [A_84,B_85] :
      ( k5_relat_1(k6_partfun1(A_84),B_85) = B_85
      | ~ r1_tarski(k1_relat_1(B_85),A_84)
      | ~ v1_relat_1(B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_20])).

tff(c_204,plain,(
    ! [B_85] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(B_85)),B_85) = B_85
      | ~ v1_relat_1(B_85) ) ),
    inference(resolution,[status(thm)],[c_6,c_195])).

tff(c_700,plain,(
    ! [A_122,B_123,C_124] :
      ( k5_relat_1(k5_relat_1(A_122,B_123),C_124) = k5_relat_1(A_122,k5_relat_1(B_123,C_124))
      | ~ v1_relat_1(C_124)
      | ~ v1_relat_1(B_123)
      | ~ v1_relat_1(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_749,plain,(
    ! [B_85,C_124] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(B_85)),k5_relat_1(B_85,C_124)) = k5_relat_1(B_85,C_124)
      | ~ v1_relat_1(C_124)
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(B_85)))
      | ~ v1_relat_1(B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_700])).

tff(c_1665,plain,(
    ! [B_166,C_167] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(B_166)),k5_relat_1(B_166,C_167)) = k5_relat_1(B_166,C_167)
      | ~ v1_relat_1(C_167)
      | ~ v1_relat_1(B_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_749])).

tff(c_1722,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),'#skF_3') = k5_relat_1('#skF_3',k6_partfun1('#skF_2'))
    | ~ v1_relat_1(k6_partfun1('#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_1665])).

tff(c_1763,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_127,c_344,c_1722])).

tff(c_18,plain,(
    ! [A_11,B_15,C_17] :
      ( k5_relat_1(k5_relat_1(A_11,B_15),C_17) = k5_relat_1(A_11,k5_relat_1(B_15,C_17))
      | ~ v1_relat_1(C_17)
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1780,plain,(
    ! [C_17] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k5_relat_1('#skF_3',C_17)) = k5_relat_1('#skF_3',C_17)
      | ~ v1_relat_1(C_17)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1763,c_18])).

tff(c_2002,plain,(
    ! [C_185] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k5_relat_1('#skF_3',C_185)) = k5_relat_1('#skF_3',C_185)
      | ~ v1_relat_1(C_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_130,c_1780])).

tff(c_2053,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1(k1_relat_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2002])).

tff(c_2090,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1(k1_relat_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_90,c_74,c_662,c_2053])).

tff(c_203,plain,(
    ! [A_6,B_7] :
      ( k5_relat_1(k6_partfun1(A_6),B_7) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_195])).

tff(c_2110,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
    | ~ v4_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2090,c_203])).

tff(c_2123,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_174,c_2110])).

tff(c_34,plain,(
    ! [A_29] :
      ( k2_relat_1(k2_funct_1(A_29)) = k1_relat_1(A_29)
      | ~ v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_277,plain,(
    ! [A_29,A_92] :
      ( k5_relat_1(k2_funct_1(A_29),k6_partfun1(A_92)) = k2_funct_1(A_29)
      | ~ r1_tarski(k1_relat_1(A_29),A_92)
      | ~ v1_relat_1(k2_funct_1(A_29))
      | ~ v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_274])).

tff(c_6135,plain,(
    ! [A_262,C_263] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_262)),C_263) = k5_relat_1(A_262,k5_relat_1(k2_funct_1(A_262),C_263))
      | ~ v1_relat_1(C_263)
      | ~ v1_relat_1(k2_funct_1(A_262))
      | ~ v1_relat_1(A_262)
      | ~ v2_funct_1(A_262)
      | ~ v1_funct_1(A_262)
      | ~ v1_relat_1(A_262) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_700])).

tff(c_84,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_1505,plain,(
    ! [C_162,B_159,D_158,A_160,E_157,F_161] :
      ( m1_subset_1(k1_partfun1(A_160,B_159,C_162,D_158,E_157,F_161),k1_zfmisc_1(k2_zfmisc_1(A_160,D_158)))
      | ~ m1_subset_1(F_161,k1_zfmisc_1(k2_zfmisc_1(C_162,D_158)))
      | ~ v1_funct_1(F_161)
      | ~ m1_subset_1(E_157,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159)))
      | ~ v1_funct_1(E_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_76,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_943,plain,(
    ! [D_129,C_130,A_131,B_132] :
      ( D_129 = C_130
      | ~ r2_relset_1(A_131,B_132,C_130,D_129)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_955,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_76,c_943])).

tff(c_976,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_955])).

tff(c_1033,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_976])).

tff(c_1518,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1505,c_1033])).

tff(c_1540,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_84,c_80,c_1518])).

tff(c_1541,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_976])).

tff(c_1980,plain,(
    ! [E_184,A_182,C_183,D_180,B_181,F_179] :
      ( k1_partfun1(A_182,B_181,C_183,D_180,E_184,F_179) = k5_relat_1(E_184,F_179)
      | ~ m1_subset_1(F_179,k1_zfmisc_1(k2_zfmisc_1(C_183,D_180)))
      | ~ v1_funct_1(F_179)
      | ~ m1_subset_1(E_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_181)))
      | ~ v1_funct_1(E_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_1990,plain,(
    ! [A_182,B_181,E_184] :
      ( k1_partfun1(A_182,B_181,'#skF_2','#skF_1',E_184,'#skF_4') = k5_relat_1(E_184,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_181)))
      | ~ v1_funct_1(E_184) ) ),
    inference(resolution,[status(thm)],[c_80,c_1980])).

tff(c_2263,plain,(
    ! [A_196,B_197,E_198] :
      ( k1_partfun1(A_196,B_197,'#skF_2','#skF_1',E_198,'#skF_4') = k5_relat_1(E_198,'#skF_4')
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197)))
      | ~ v1_funct_1(E_198) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1990])).

tff(c_2278,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_2263])).

tff(c_2290,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1541,c_2278])).

tff(c_765,plain,(
    ! [B_85,C_124] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(B_85)),k5_relat_1(B_85,C_124)) = k5_relat_1(B_85,C_124)
      | ~ v1_relat_1(C_124)
      | ~ v1_relat_1(B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_749])).

tff(c_2300,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_1')) = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2290,c_765])).

tff(c_2309,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_1')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_133,c_2290,c_2300])).

tff(c_6182,plain,
    ( k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1'))) = k6_partfun1('#skF_1')
    | ~ v1_relat_1(k6_partfun1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6135,c_2309])).

tff(c_6371,plain,(
    k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1'))) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_90,c_74,c_130,c_662,c_127,c_6182])).

tff(c_6482,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_6371])).

tff(c_6494,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_90,c_74,c_662,c_2123,c_6482])).

tff(c_6552,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_6494])).

tff(c_6636,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_6552])).

tff(c_6640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_175,c_6636])).

tff(c_6641,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_6494])).

tff(c_16,plain,(
    ! [A_10] :
      ( k9_relat_1(A_10,k1_relat_1(A_10)) = k2_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_663,plain,(
    ! [B_119,A_120] :
      ( k10_relat_1(B_119,k9_relat_1(B_119,A_120)) = A_120
      | ~ v2_funct_1(B_119)
      | ~ r1_tarski(A_120,k1_relat_1(B_119))
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_674,plain,(
    ! [B_121] :
      ( k10_relat_1(B_121,k9_relat_1(B_121,k1_relat_1(B_121))) = k1_relat_1(B_121)
      | ~ v2_funct_1(B_121)
      | ~ v1_funct_1(B_121)
      | ~ v1_relat_1(B_121) ) ),
    inference(resolution,[status(thm)],[c_6,c_663])).

tff(c_977,plain,(
    ! [A_133] :
      ( k10_relat_1(A_133,k2_relat_1(A_133)) = k1_relat_1(A_133)
      | ~ v2_funct_1(A_133)
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_674])).

tff(c_993,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_977])).

tff(c_1002,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_130,c_90,c_74,c_993])).

tff(c_2531,plain,(
    ! [A_203] :
      ( k9_relat_1(k2_funct_1(A_203),k2_relat_1(A_203)) = k2_relat_1(k2_funct_1(A_203))
      | ~ v1_relat_1(k2_funct_1(A_203))
      | ~ v2_funct_1(A_203)
      | ~ v1_funct_1(A_203)
      | ~ v1_relat_1(A_203) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_16])).

tff(c_2547,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_2531])).

tff(c_2554,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_90,c_74,c_662,c_2547])).

tff(c_30,plain,(
    ! [B_26,A_25] :
      ( k9_relat_1(k2_funct_1(B_26),A_25) = k10_relat_1(B_26,A_25)
      | ~ v2_funct_1(B_26)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2568,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2554,c_30])).

tff(c_2575,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_90,c_74,c_1002,c_2568])).

tff(c_2612,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2575,c_282])).

tff(c_2648,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_2612])).

tff(c_6663,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6641,c_2648])).

tff(c_38,plain,(
    ! [A_30] :
      ( k5_relat_1(k2_funct_1(A_30),A_30) = k6_relat_1(k2_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_93,plain,(
    ! [A_30] :
      ( k5_relat_1(k2_funct_1(A_30),A_30) = k6_partfun1(k2_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_38])).

tff(c_5522,plain,(
    ! [A_253,C_254] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_253)),C_254) = k5_relat_1(k2_funct_1(A_253),k5_relat_1(A_253,C_254))
      | ~ v1_relat_1(C_254)
      | ~ v1_relat_1(A_253)
      | ~ v1_relat_1(k2_funct_1(A_253))
      | ~ v2_funct_1(A_253)
      | ~ v1_funct_1(A_253)
      | ~ v1_relat_1(A_253) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_700])).

tff(c_5708,plain,(
    ! [C_254] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_254)) = k5_relat_1(k6_partfun1('#skF_2'),C_254)
      | ~ v1_relat_1(C_254)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_5522])).

tff(c_9368,plain,(
    ! [C_327] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_327)) = k5_relat_1(k6_partfun1('#skF_2'),C_327)
      | ~ v1_relat_1(C_327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_90,c_74,c_662,c_130,c_5708])).

tff(c_9431,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2290,c_9368])).

tff(c_9498,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_6663,c_9431])).

tff(c_9542,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9498,c_203])).

tff(c_9565,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_176,c_9542])).

tff(c_9567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_9565])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:42:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.44/3.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.44/3.43  
% 9.44/3.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.44/3.43  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.44/3.43  
% 9.44/3.43  %Foreground sorts:
% 9.44/3.43  
% 9.44/3.43  
% 9.44/3.43  %Background operators:
% 9.44/3.43  
% 9.44/3.43  
% 9.44/3.43  %Foreground operators:
% 9.44/3.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.44/3.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.44/3.43  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.44/3.43  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.44/3.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.44/3.43  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.44/3.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.44/3.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.44/3.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.44/3.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.44/3.43  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.44/3.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.44/3.43  tff('#skF_2', type, '#skF_2': $i).
% 9.44/3.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.44/3.43  tff('#skF_3', type, '#skF_3': $i).
% 9.44/3.43  tff('#skF_1', type, '#skF_1': $i).
% 9.44/3.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.44/3.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.44/3.43  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.44/3.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.44/3.43  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.44/3.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.44/3.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.44/3.43  tff('#skF_4', type, '#skF_4': $i).
% 9.44/3.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.44/3.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.44/3.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.44/3.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.44/3.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.44/3.43  
% 9.44/3.46  tff(f_206, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 9.44/3.46  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.44/3.46  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.44/3.46  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.44/3.46  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 9.44/3.46  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.44/3.46  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.44/3.46  tff(f_116, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 9.44/3.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.44/3.46  tff(f_170, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.44/3.46  tff(f_146, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 9.44/3.46  tff(f_126, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 9.44/3.46  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 9.44/3.46  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 9.44/3.46  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 9.44/3.46  tff(f_158, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.44/3.46  tff(f_144, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.44/3.46  tff(f_168, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.44/3.46  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 9.44/3.46  tff(f_106, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 9.44/3.46  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 9.44/3.46  tff(c_68, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.44/3.46  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.44/3.46  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.44/3.46  tff(c_115, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.44/3.46  tff(c_124, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_80, c_115])).
% 9.44/3.46  tff(c_133, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_124])).
% 9.44/3.46  tff(c_164, plain, (![C_73, A_74, B_75]: (v4_relat_1(C_73, A_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.44/3.46  tff(c_176, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_80, c_164])).
% 9.44/3.46  tff(c_86, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.44/3.46  tff(c_121, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_86, c_115])).
% 9.44/3.46  tff(c_130, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_121])).
% 9.44/3.46  tff(c_175, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_86, c_164])).
% 9.44/3.46  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.44/3.46  tff(c_90, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.44/3.46  tff(c_74, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.44/3.46  tff(c_26, plain, (![A_22]: (v1_relat_1(k2_funct_1(A_22)) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.44/3.46  tff(c_78, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.44/3.46  tff(c_317, plain, (![A_97, B_98, C_99]: (k2_relset_1(A_97, B_98, C_99)=k2_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 9.44/3.46  tff(c_323, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_317])).
% 9.44/3.46  tff(c_329, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_323])).
% 9.44/3.46  tff(c_244, plain, (![A_90]: (k1_relat_1(k2_funct_1(A_90))=k2_relat_1(A_90) | ~v2_funct_1(A_90) | ~v1_funct_1(A_90) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.44/3.46  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.44/3.46  tff(c_183, plain, (![B_80, A_81]: (v4_relat_1(B_80, A_81) | ~r1_tarski(k1_relat_1(B_80), A_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.44/3.46  tff(c_192, plain, (![B_80]: (v4_relat_1(B_80, k1_relat_1(B_80)) | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_6, c_183])).
% 9.44/3.46  tff(c_644, plain, (![A_118]: (v4_relat_1(k2_funct_1(A_118), k2_relat_1(A_118)) | ~v1_relat_1(k2_funct_1(A_118)) | ~v2_funct_1(A_118) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(superposition, [status(thm), theory('equality')], [c_244, c_192])).
% 9.44/3.46  tff(c_647, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_329, c_644])).
% 9.44/3.46  tff(c_652, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_90, c_74, c_647])).
% 9.44/3.46  tff(c_653, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_652])).
% 9.44/3.46  tff(c_656, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_653])).
% 9.44/3.46  tff(c_660, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_90, c_656])).
% 9.44/3.46  tff(c_662, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_652])).
% 9.44/3.46  tff(c_60, plain, (![A_54]: (k6_relat_1(A_54)=k6_partfun1(A_54))), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.44/3.46  tff(c_52, plain, (![A_41]: (m1_subset_1(k6_relat_1(A_41), k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.44/3.46  tff(c_91, plain, (![A_41]: (m1_subset_1(k6_partfun1(A_41), k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_52])).
% 9.44/3.46  tff(c_118, plain, (![A_41]: (v1_relat_1(k6_partfun1(A_41)) | ~v1_relat_1(k2_zfmisc_1(A_41, A_41)))), inference(resolution, [status(thm)], [c_91, c_115])).
% 9.44/3.46  tff(c_127, plain, (![A_41]: (v1_relat_1(k6_partfun1(A_41)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_118])).
% 9.44/3.46  tff(c_174, plain, (![A_41]: (v4_relat_1(k6_partfun1(A_41), A_41))), inference(resolution, [status(thm)], [c_91, c_164])).
% 9.44/3.46  tff(c_40, plain, (![A_30]: (k5_relat_1(A_30, k2_funct_1(A_30))=k6_relat_1(k1_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.44/3.46  tff(c_92, plain, (![A_30]: (k5_relat_1(A_30, k2_funct_1(A_30))=k6_partfun1(k1_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_40])).
% 9.44/3.46  tff(c_22, plain, (![B_21, A_20]: (k5_relat_1(B_21, k6_relat_1(A_20))=B_21 | ~r1_tarski(k2_relat_1(B_21), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.44/3.46  tff(c_274, plain, (![B_91, A_92]: (k5_relat_1(B_91, k6_partfun1(A_92))=B_91 | ~r1_tarski(k2_relat_1(B_91), A_92) | ~v1_relat_1(B_91))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_22])).
% 9.44/3.46  tff(c_282, plain, (![B_91]: (k5_relat_1(B_91, k6_partfun1(k2_relat_1(B_91)))=B_91 | ~v1_relat_1(B_91))), inference(resolution, [status(thm)], [c_6, c_274])).
% 9.44/3.46  tff(c_334, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_329, c_282])).
% 9.44/3.46  tff(c_344, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_334])).
% 9.44/3.46  tff(c_20, plain, (![A_18, B_19]: (k5_relat_1(k6_relat_1(A_18), B_19)=B_19 | ~r1_tarski(k1_relat_1(B_19), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.44/3.46  tff(c_195, plain, (![A_84, B_85]: (k5_relat_1(k6_partfun1(A_84), B_85)=B_85 | ~r1_tarski(k1_relat_1(B_85), A_84) | ~v1_relat_1(B_85))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_20])).
% 9.44/3.46  tff(c_204, plain, (![B_85]: (k5_relat_1(k6_partfun1(k1_relat_1(B_85)), B_85)=B_85 | ~v1_relat_1(B_85))), inference(resolution, [status(thm)], [c_6, c_195])).
% 9.44/3.46  tff(c_700, plain, (![A_122, B_123, C_124]: (k5_relat_1(k5_relat_1(A_122, B_123), C_124)=k5_relat_1(A_122, k5_relat_1(B_123, C_124)) | ~v1_relat_1(C_124) | ~v1_relat_1(B_123) | ~v1_relat_1(A_122))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.44/3.46  tff(c_749, plain, (![B_85, C_124]: (k5_relat_1(k6_partfun1(k1_relat_1(B_85)), k5_relat_1(B_85, C_124))=k5_relat_1(B_85, C_124) | ~v1_relat_1(C_124) | ~v1_relat_1(B_85) | ~v1_relat_1(k6_partfun1(k1_relat_1(B_85))) | ~v1_relat_1(B_85))), inference(superposition, [status(thm), theory('equality')], [c_204, c_700])).
% 9.44/3.46  tff(c_1665, plain, (![B_166, C_167]: (k5_relat_1(k6_partfun1(k1_relat_1(B_166)), k5_relat_1(B_166, C_167))=k5_relat_1(B_166, C_167) | ~v1_relat_1(C_167) | ~v1_relat_1(B_166))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_749])).
% 9.44/3.46  tff(c_1722, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), '#skF_3')=k5_relat_1('#skF_3', k6_partfun1('#skF_2')) | ~v1_relat_1(k6_partfun1('#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_344, c_1665])).
% 9.44/3.46  tff(c_1763, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_127, c_344, c_1722])).
% 9.44/3.46  tff(c_18, plain, (![A_11, B_15, C_17]: (k5_relat_1(k5_relat_1(A_11, B_15), C_17)=k5_relat_1(A_11, k5_relat_1(B_15, C_17)) | ~v1_relat_1(C_17) | ~v1_relat_1(B_15) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.44/3.46  tff(c_1780, plain, (![C_17]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k5_relat_1('#skF_3', C_17))=k5_relat_1('#skF_3', C_17) | ~v1_relat_1(C_17) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_1763, c_18])).
% 9.44/3.46  tff(c_2002, plain, (![C_185]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k5_relat_1('#skF_3', C_185))=k5_relat_1('#skF_3', C_185) | ~v1_relat_1(C_185))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_130, c_1780])).
% 9.44/3.46  tff(c_2053, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1(k1_relat_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_92, c_2002])).
% 9.44/3.46  tff(c_2090, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1(k1_relat_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_90, c_74, c_662, c_2053])).
% 9.44/3.46  tff(c_203, plain, (![A_6, B_7]: (k5_relat_1(k6_partfun1(A_6), B_7)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_12, c_195])).
% 9.44/3.46  tff(c_2110, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | ~v4_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2090, c_203])).
% 9.44/3.46  tff(c_2123, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_174, c_2110])).
% 9.44/3.46  tff(c_34, plain, (![A_29]: (k2_relat_1(k2_funct_1(A_29))=k1_relat_1(A_29) | ~v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.44/3.46  tff(c_277, plain, (![A_29, A_92]: (k5_relat_1(k2_funct_1(A_29), k6_partfun1(A_92))=k2_funct_1(A_29) | ~r1_tarski(k1_relat_1(A_29), A_92) | ~v1_relat_1(k2_funct_1(A_29)) | ~v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(superposition, [status(thm), theory('equality')], [c_34, c_274])).
% 9.44/3.46  tff(c_6135, plain, (![A_262, C_263]: (k5_relat_1(k6_partfun1(k1_relat_1(A_262)), C_263)=k5_relat_1(A_262, k5_relat_1(k2_funct_1(A_262), C_263)) | ~v1_relat_1(C_263) | ~v1_relat_1(k2_funct_1(A_262)) | ~v1_relat_1(A_262) | ~v2_funct_1(A_262) | ~v1_funct_1(A_262) | ~v1_relat_1(A_262))), inference(superposition, [status(thm), theory('equality')], [c_92, c_700])).
% 9.44/3.46  tff(c_84, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.44/3.46  tff(c_1505, plain, (![C_162, B_159, D_158, A_160, E_157, F_161]: (m1_subset_1(k1_partfun1(A_160, B_159, C_162, D_158, E_157, F_161), k1_zfmisc_1(k2_zfmisc_1(A_160, D_158))) | ~m1_subset_1(F_161, k1_zfmisc_1(k2_zfmisc_1(C_162, D_158))) | ~v1_funct_1(F_161) | ~m1_subset_1(E_157, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))) | ~v1_funct_1(E_157))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.44/3.46  tff(c_76, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.44/3.46  tff(c_943, plain, (![D_129, C_130, A_131, B_132]: (D_129=C_130 | ~r2_relset_1(A_131, B_132, C_130, D_129) | ~m1_subset_1(D_129, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.44/3.46  tff(c_955, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_76, c_943])).
% 9.44/3.46  tff(c_976, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_955])).
% 9.44/3.46  tff(c_1033, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_976])).
% 9.44/3.46  tff(c_1518, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1505, c_1033])).
% 9.44/3.46  tff(c_1540, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_84, c_80, c_1518])).
% 9.44/3.46  tff(c_1541, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_976])).
% 9.44/3.46  tff(c_1980, plain, (![E_184, A_182, C_183, D_180, B_181, F_179]: (k1_partfun1(A_182, B_181, C_183, D_180, E_184, F_179)=k5_relat_1(E_184, F_179) | ~m1_subset_1(F_179, k1_zfmisc_1(k2_zfmisc_1(C_183, D_180))) | ~v1_funct_1(F_179) | ~m1_subset_1(E_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_181))) | ~v1_funct_1(E_184))), inference(cnfTransformation, [status(thm)], [f_168])).
% 9.44/3.46  tff(c_1990, plain, (![A_182, B_181, E_184]: (k1_partfun1(A_182, B_181, '#skF_2', '#skF_1', E_184, '#skF_4')=k5_relat_1(E_184, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_181))) | ~v1_funct_1(E_184))), inference(resolution, [status(thm)], [c_80, c_1980])).
% 9.44/3.46  tff(c_2263, plain, (![A_196, B_197, E_198]: (k1_partfun1(A_196, B_197, '#skF_2', '#skF_1', E_198, '#skF_4')=k5_relat_1(E_198, '#skF_4') | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))) | ~v1_funct_1(E_198))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1990])).
% 9.44/3.46  tff(c_2278, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_2263])).
% 9.44/3.46  tff(c_2290, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1541, c_2278])).
% 9.44/3.46  tff(c_765, plain, (![B_85, C_124]: (k5_relat_1(k6_partfun1(k1_relat_1(B_85)), k5_relat_1(B_85, C_124))=k5_relat_1(B_85, C_124) | ~v1_relat_1(C_124) | ~v1_relat_1(B_85))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_749])).
% 9.44/3.46  tff(c_2300, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_1'))=k5_relat_1('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2290, c_765])).
% 9.44/3.46  tff(c_2309, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_1'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_133, c_2290, c_2300])).
% 9.44/3.46  tff(c_6182, plain, (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1')))=k6_partfun1('#skF_1') | ~v1_relat_1(k6_partfun1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6135, c_2309])).
% 9.44/3.46  tff(c_6371, plain, (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1')))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_90, c_74, c_130, c_662, c_127, c_6182])).
% 9.44/3.46  tff(c_6482, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_277, c_6371])).
% 9.44/3.46  tff(c_6494, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_90, c_74, c_662, c_2123, c_6482])).
% 9.44/3.46  tff(c_6552, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_6494])).
% 9.44/3.46  tff(c_6636, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_6552])).
% 9.44/3.46  tff(c_6640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_175, c_6636])).
% 9.44/3.46  tff(c_6641, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_6494])).
% 9.44/3.46  tff(c_16, plain, (![A_10]: (k9_relat_1(A_10, k1_relat_1(A_10))=k2_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.44/3.46  tff(c_663, plain, (![B_119, A_120]: (k10_relat_1(B_119, k9_relat_1(B_119, A_120))=A_120 | ~v2_funct_1(B_119) | ~r1_tarski(A_120, k1_relat_1(B_119)) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.44/3.46  tff(c_674, plain, (![B_121]: (k10_relat_1(B_121, k9_relat_1(B_121, k1_relat_1(B_121)))=k1_relat_1(B_121) | ~v2_funct_1(B_121) | ~v1_funct_1(B_121) | ~v1_relat_1(B_121))), inference(resolution, [status(thm)], [c_6, c_663])).
% 9.44/3.46  tff(c_977, plain, (![A_133]: (k10_relat_1(A_133, k2_relat_1(A_133))=k1_relat_1(A_133) | ~v2_funct_1(A_133) | ~v1_funct_1(A_133) | ~v1_relat_1(A_133) | ~v1_relat_1(A_133))), inference(superposition, [status(thm), theory('equality')], [c_16, c_674])).
% 9.44/3.46  tff(c_993, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_329, c_977])).
% 9.44/3.46  tff(c_1002, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_130, c_90, c_74, c_993])).
% 9.44/3.46  tff(c_2531, plain, (![A_203]: (k9_relat_1(k2_funct_1(A_203), k2_relat_1(A_203))=k2_relat_1(k2_funct_1(A_203)) | ~v1_relat_1(k2_funct_1(A_203)) | ~v2_funct_1(A_203) | ~v1_funct_1(A_203) | ~v1_relat_1(A_203))), inference(superposition, [status(thm), theory('equality')], [c_244, c_16])).
% 9.44/3.46  tff(c_2547, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_329, c_2531])).
% 9.44/3.46  tff(c_2554, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_90, c_74, c_662, c_2547])).
% 9.44/3.46  tff(c_30, plain, (![B_26, A_25]: (k9_relat_1(k2_funct_1(B_26), A_25)=k10_relat_1(B_26, A_25) | ~v2_funct_1(B_26) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.44/3.46  tff(c_2568, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2554, c_30])).
% 9.44/3.46  tff(c_2575, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_90, c_74, c_1002, c_2568])).
% 9.44/3.46  tff(c_2612, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2575, c_282])).
% 9.44/3.46  tff(c_2648, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_662, c_2612])).
% 9.44/3.46  tff(c_6663, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6641, c_2648])).
% 9.44/3.46  tff(c_38, plain, (![A_30]: (k5_relat_1(k2_funct_1(A_30), A_30)=k6_relat_1(k2_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.44/3.46  tff(c_93, plain, (![A_30]: (k5_relat_1(k2_funct_1(A_30), A_30)=k6_partfun1(k2_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_38])).
% 9.44/3.46  tff(c_5522, plain, (![A_253, C_254]: (k5_relat_1(k6_partfun1(k2_relat_1(A_253)), C_254)=k5_relat_1(k2_funct_1(A_253), k5_relat_1(A_253, C_254)) | ~v1_relat_1(C_254) | ~v1_relat_1(A_253) | ~v1_relat_1(k2_funct_1(A_253)) | ~v2_funct_1(A_253) | ~v1_funct_1(A_253) | ~v1_relat_1(A_253))), inference(superposition, [status(thm), theory('equality')], [c_93, c_700])).
% 9.44/3.46  tff(c_5708, plain, (![C_254]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_254))=k5_relat_1(k6_partfun1('#skF_2'), C_254) | ~v1_relat_1(C_254) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_329, c_5522])).
% 9.44/3.46  tff(c_9368, plain, (![C_327]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_327))=k5_relat_1(k6_partfun1('#skF_2'), C_327) | ~v1_relat_1(C_327))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_90, c_74, c_662, c_130, c_5708])).
% 9.44/3.46  tff(c_9431, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2290, c_9368])).
% 9.44/3.46  tff(c_9498, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_6663, c_9431])).
% 9.44/3.46  tff(c_9542, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9498, c_203])).
% 9.44/3.46  tff(c_9565, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_176, c_9542])).
% 9.44/3.46  tff(c_9567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_9565])).
% 9.44/3.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.44/3.46  
% 9.44/3.46  Inference rules
% 9.44/3.46  ----------------------
% 9.44/3.46  #Ref     : 0
% 9.44/3.46  #Sup     : 2019
% 9.44/3.46  #Fact    : 0
% 9.44/3.46  #Define  : 0
% 9.44/3.46  #Split   : 11
% 9.44/3.46  #Chain   : 0
% 9.44/3.46  #Close   : 0
% 9.44/3.46  
% 9.44/3.46  Ordering : KBO
% 9.44/3.46  
% 9.44/3.46  Simplification rules
% 9.44/3.46  ----------------------
% 9.44/3.46  #Subsume      : 65
% 9.44/3.46  #Demod        : 3017
% 9.44/3.46  #Tautology    : 763
% 9.44/3.46  #SimpNegUnit  : 2
% 9.44/3.46  #BackRed      : 39
% 9.44/3.46  
% 9.44/3.46  #Partial instantiations: 0
% 9.44/3.46  #Strategies tried      : 1
% 9.44/3.46  
% 9.44/3.46  Timing (in seconds)
% 9.44/3.46  ----------------------
% 9.44/3.46  Preprocessing        : 0.38
% 9.44/3.46  Parsing              : 0.21
% 9.44/3.46  CNF conversion       : 0.03
% 9.44/3.46  Main loop            : 2.29
% 9.44/3.46  Inferencing          : 0.63
% 9.44/3.46  Reduction            : 1.09
% 9.44/3.46  Demodulation         : 0.89
% 9.44/3.46  BG Simplification    : 0.07
% 9.44/3.46  Subsumption          : 0.38
% 9.44/3.46  Abstraction          : 0.08
% 9.44/3.46  MUC search           : 0.00
% 9.44/3.46  Cooper               : 0.00
% 9.44/3.46  Total                : 2.71
% 9.44/3.46  Index Insertion      : 0.00
% 9.44/3.46  Index Deletion       : 0.00
% 9.44/3.46  Index Matching       : 0.00
% 9.44/3.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
