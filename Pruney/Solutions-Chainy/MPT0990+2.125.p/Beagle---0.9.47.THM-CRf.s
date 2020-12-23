%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:14 EST 2020

% Result     : Theorem 11.56s
% Output     : CNFRefutation 11.62s
% Verified   : 
% Statistics : Number of formulae       :  201 (3126 expanded)
%              Number of leaves         :   51 (1096 expanded)
%              Depth                    :   28
%              Number of atoms          :  449 (9988 expanded)
%              Number of equality atoms :  100 (2593 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_188,negated_conjecture,(
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_152,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_140,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_162,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_136,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_124,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_150,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_62,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_116,plain,(
    ! [B_60,A_61] :
      ( v1_relat_1(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_125,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_74,c_116])).

tff(c_134,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_125])).

tff(c_164,plain,(
    ! [C_71,A_72,B_73] :
      ( v4_relat_1(C_71,A_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_176,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_164])).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_122,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_80,c_116])).

tff(c_131,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_122])).

tff(c_175,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_164])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_84,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_68,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_22,plain,(
    ! [A_21] :
      ( v1_relat_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54,plain,(
    ! [A_49] : k6_relat_1(A_49) = k6_partfun1(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_32,plain,(
    ! [A_25] :
      ( k5_relat_1(A_25,k2_funct_1(A_25)) = k6_relat_1(k1_relat_1(A_25))
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_85,plain,(
    ! [A_25] :
      ( k5_relat_1(A_25,k2_funct_1(A_25)) = k6_partfun1(k1_relat_1(A_25))
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_32])).

tff(c_50,plain,(
    ! [A_42] : m1_subset_1(k6_partfun1(A_42),k1_zfmisc_1(k2_zfmisc_1(A_42,A_42))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_119,plain,(
    ! [A_42] :
      ( v1_relat_1(k6_partfun1(A_42))
      | ~ v1_relat_1(k2_zfmisc_1(A_42,A_42)) ) ),
    inference(resolution,[status(thm)],[c_50,c_116])).

tff(c_128,plain,(
    ! [A_42] : v1_relat_1(k6_partfun1(A_42)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_119])).

tff(c_72,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_248,plain,(
    ! [A_89,B_90,C_91] :
      ( k2_relset_1(A_89,B_90,C_91) = k2_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_254,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_248])).

tff(c_260,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_254])).

tff(c_194,plain,(
    ! [A_81] :
      ( k1_relat_1(k2_funct_1(A_81)) = k2_relat_1(A_81)
      | ~ v2_funct_1(A_81)
      | ~ v1_funct_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_10,plain,(
    ! [A_8] :
      ( k9_relat_1(A_8,k1_relat_1(A_8)) = k2_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_926,plain,(
    ! [A_154] :
      ( k9_relat_1(k2_funct_1(A_154),k2_relat_1(A_154)) = k2_relat_1(k2_funct_1(A_154))
      | ~ v1_relat_1(k2_funct_1(A_154))
      | ~ v2_funct_1(A_154)
      | ~ v1_funct_1(A_154)
      | ~ v1_relat_1(A_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_10])).

tff(c_942,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_926])).

tff(c_949,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_84,c_68,c_942])).

tff(c_950,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_949])).

tff(c_953,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_950])).

tff(c_957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_84,c_953])).

tff(c_959,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_949])).

tff(c_28,plain,(
    ! [A_24] :
      ( k1_relat_1(k2_funct_1(A_24)) = k2_relat_1(A_24)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20,plain,(
    ! [A_21] :
      ( v1_funct_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [A_9] :
      ( k10_relat_1(A_9,k2_relat_1(A_9)) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_302,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_12])).

tff(c_312,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_302])).

tff(c_958,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_949])).

tff(c_24,plain,(
    ! [B_23,A_22] :
      ( k9_relat_1(k2_funct_1(B_23),A_22) = k10_relat_1(B_23,A_22)
      | ~ v2_funct_1(B_23)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_985,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_958,c_24])).

tff(c_992,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_84,c_68,c_312,c_985])).

tff(c_262,plain,(
    ! [A_92] :
      ( m1_subset_1(A_92,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_92),k2_relat_1(A_92))))
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_34,plain,(
    ! [C_28,B_27,A_26] :
      ( v5_relat_1(C_28,B_27)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_286,plain,(
    ! [A_92] :
      ( v5_relat_1(A_92,k2_relat_1(A_92))
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(resolution,[status(thm)],[c_262,c_34])).

tff(c_1009,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_992,c_286])).

tff(c_1037,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_959,c_1009])).

tff(c_1121,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1037])).

tff(c_1124,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1121])).

tff(c_1128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_84,c_1124])).

tff(c_1130,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1037])).

tff(c_56,plain,(
    ! [A_50] :
      ( m1_subset_1(A_50,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_50),k2_relat_1(A_50))))
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1012,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_992,c_56])).

tff(c_1039,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_959,c_1012])).

tff(c_1990,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_1039])).

tff(c_36,plain,(
    ! [C_28,A_26,B_27] :
      ( v4_relat_1(C_28,A_26)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2050,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1990,c_36])).

tff(c_2063,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2050])).

tff(c_2068,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_84,c_68,c_260,c_2063])).

tff(c_209,plain,(
    ! [A_81,A_4] :
      ( r1_tarski(k2_relat_1(A_81),A_4)
      | ~ v4_relat_1(k2_funct_1(A_81),A_4)
      | ~ v1_relat_1(k2_funct_1(A_81))
      | ~ v2_funct_1(A_81)
      | ~ v1_funct_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_6])).

tff(c_2123,plain,
    ( r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2068,c_209])).

tff(c_2126,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_84,c_68,c_959,c_260,c_2123])).

tff(c_18,plain,(
    ! [B_20,A_19] :
      ( k5_relat_1(B_20,k6_relat_1(A_19)) = B_20
      | ~ r1_tarski(k2_relat_1(B_20),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_87,plain,(
    ! [B_20,A_19] :
      ( k5_relat_1(B_20,k6_partfun1(A_19)) = B_20
      | ~ r1_tarski(k2_relat_1(B_20),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_18])).

tff(c_296,plain,(
    ! [A_19] :
      ( k5_relat_1('#skF_3',k6_partfun1(A_19)) = '#skF_3'
      | ~ r1_tarski('#skF_2',A_19)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_87])).

tff(c_308,plain,(
    ! [A_19] :
      ( k5_relat_1('#skF_3',k6_partfun1(A_19)) = '#skF_3'
      | ~ r1_tarski('#skF_2',A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_296])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( k5_relat_1(k6_relat_1(A_17),B_18) = B_18
      | ~ r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_180,plain,(
    ! [A_77,B_78] :
      ( k5_relat_1(k6_partfun1(A_77),B_78) = B_78
      | ~ r1_tarski(k1_relat_1(B_78),A_77)
      | ~ v1_relat_1(B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_16])).

tff(c_184,plain,(
    ! [A_4,B_5] :
      ( k5_relat_1(k6_partfun1(A_4),B_5) = B_5
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_180])).

tff(c_397,plain,(
    ! [A_99,B_100,C_101] :
      ( k5_relat_1(k5_relat_1(A_99,B_100),C_101) = k5_relat_1(A_99,k5_relat_1(B_100,C_101))
      | ~ v1_relat_1(C_101)
      | ~ v1_relat_1(B_100)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_415,plain,(
    ! [A_4,B_5,C_101] :
      ( k5_relat_1(k6_partfun1(A_4),k5_relat_1(B_5,C_101)) = k5_relat_1(B_5,C_101)
      | ~ v1_relat_1(C_101)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(k6_partfun1(A_4))
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_397])).

tff(c_556,plain,(
    ! [A_112,B_113,C_114] :
      ( k5_relat_1(k6_partfun1(A_112),k5_relat_1(B_113,C_114)) = k5_relat_1(B_113,C_114)
      | ~ v1_relat_1(C_114)
      | ~ v4_relat_1(B_113,A_112)
      | ~ v1_relat_1(B_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_415])).

tff(c_592,plain,(
    ! [A_112,A_19] :
      ( k5_relat_1(k6_partfun1(A_112),'#skF_3') = k5_relat_1('#skF_3',k6_partfun1(A_19))
      | ~ v1_relat_1(k6_partfun1(A_19))
      | ~ v4_relat_1('#skF_3',A_112)
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski('#skF_2',A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_556])).

tff(c_617,plain,(
    ! [A_115,A_116] :
      ( k5_relat_1(k6_partfun1(A_115),'#skF_3') = k5_relat_1('#skF_3',k6_partfun1(A_116))
      | ~ v4_relat_1('#skF_3',A_115)
      | ~ r1_tarski('#skF_2',A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_128,c_592])).

tff(c_641,plain,(
    ! [A_115,A_116] :
      ( k5_relat_1(k6_partfun1(A_115),'#skF_3') = '#skF_3'
      | ~ r1_tarski('#skF_2',A_116)
      | ~ v4_relat_1('#skF_3',A_115)
      | ~ r1_tarski('#skF_2',A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_617,c_308])).

tff(c_672,plain,(
    ! [A_116] :
      ( ~ r1_tarski('#skF_2',A_116)
      | ~ r1_tarski('#skF_2',A_116) ) ),
    inference(splitLeft,[status(thm)],[c_641])).

tff(c_2128,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_2126,c_672])).

tff(c_2132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2126,c_2128])).

tff(c_2134,plain,(
    ! [A_208] :
      ( k5_relat_1(k6_partfun1(A_208),'#skF_3') = '#skF_3'
      | ~ v4_relat_1('#skF_3',A_208) ) ),
    inference(splitRight,[status(thm)],[c_641])).

tff(c_14,plain,(
    ! [A_10,B_14,C_16] :
      ( k5_relat_1(k5_relat_1(A_10,B_14),C_16) = k5_relat_1(A_10,k5_relat_1(B_14,C_16))
      | ~ v1_relat_1(C_16)
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2149,plain,(
    ! [A_208,C_16] :
      ( k5_relat_1(k6_partfun1(A_208),k5_relat_1('#skF_3',C_16)) = k5_relat_1('#skF_3',C_16)
      | ~ v1_relat_1(C_16)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k6_partfun1(A_208))
      | ~ v4_relat_1('#skF_3',A_208) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2134,c_14])).

tff(c_2910,plain,(
    ! [A_254,C_255] :
      ( k5_relat_1(k6_partfun1(A_254),k5_relat_1('#skF_3',C_255)) = k5_relat_1('#skF_3',C_255)
      | ~ v1_relat_1(C_255)
      | ~ v4_relat_1('#skF_3',A_254) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_131,c_2149])).

tff(c_2951,plain,(
    ! [A_254] :
      ( k5_relat_1(k6_partfun1(A_254),k6_partfun1(k1_relat_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v4_relat_1('#skF_3',A_254)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_2910])).

tff(c_2980,plain,(
    ! [A_254] :
      ( k5_relat_1(k6_partfun1(A_254),k6_partfun1(k1_relat_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v4_relat_1('#skF_3',A_254) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_84,c_68,c_2951])).

tff(c_2997,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2980])).

tff(c_3022,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_2997])).

tff(c_3026,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_84,c_3022])).

tff(c_3028,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2980])).

tff(c_293,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_56])).

tff(c_306,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_84,c_293])).

tff(c_339,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_306,c_36])).

tff(c_174,plain,(
    ! [A_42] : v4_relat_1(k6_partfun1(A_42),A_42) ),
    inference(resolution,[status(thm)],[c_50,c_164])).

tff(c_3029,plain,(
    ! [A_264] :
      ( k5_relat_1(k6_partfun1(A_264),k6_partfun1(k1_relat_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
      | ~ v4_relat_1('#skF_3',A_264) ) ),
    inference(splitRight,[status(thm)],[c_2980])).

tff(c_3051,plain,(
    ! [A_4] :
      ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
      | ~ v4_relat_1('#skF_3',A_4)
      | ~ v4_relat_1(k6_partfun1(k1_relat_1('#skF_3')),A_4)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_3029])).

tff(c_3063,plain,(
    ! [A_4] :
      ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
      | ~ v4_relat_1('#skF_3',A_4)
      | ~ v4_relat_1(k6_partfun1(k1_relat_1('#skF_3')),A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_3051])).

tff(c_5840,plain,(
    ! [A_338] :
      ( ~ v4_relat_1('#skF_3',A_338)
      | ~ v4_relat_1(k6_partfun1(k1_relat_1('#skF_3')),A_338) ) ),
    inference(splitLeft,[status(thm)],[c_3063])).

tff(c_5848,plain,(
    ~ v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_174,c_5840])).

tff(c_5855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_5848])).

tff(c_5856,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3063])).

tff(c_230,plain,(
    ! [A_88] :
      ( k2_relat_1(k2_funct_1(A_88)) = k1_relat_1(A_88)
      | ~ v2_funct_1(A_88)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_7546,plain,(
    ! [A_390,A_391] :
      ( k5_relat_1(k2_funct_1(A_390),k6_partfun1(A_391)) = k2_funct_1(A_390)
      | ~ r1_tarski(k1_relat_1(A_390),A_391)
      | ~ v1_relat_1(k2_funct_1(A_390))
      | ~ v2_funct_1(A_390)
      | ~ v1_funct_1(A_390)
      | ~ v1_relat_1(A_390) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_87])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_2782,plain,(
    ! [B_248,C_249,A_246,D_247,F_245,E_250] :
      ( m1_subset_1(k1_partfun1(A_246,B_248,C_249,D_247,E_250,F_245),k1_zfmisc_1(k2_zfmisc_1(A_246,D_247)))
      | ~ m1_subset_1(F_245,k1_zfmisc_1(k2_zfmisc_1(C_249,D_247)))
      | ~ v1_funct_1(F_245)
      | ~ m1_subset_1(E_250,k1_zfmisc_1(k2_zfmisc_1(A_246,B_248)))
      | ~ v1_funct_1(E_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_522,plain,(
    ! [D_108,C_109,A_110,B_111] :
      ( D_108 = C_109
      | ~ r2_relset_1(A_110,B_111,C_109,D_108)
      | ~ m1_subset_1(D_108,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_534,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_522])).

tff(c_555,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_534])).

tff(c_2178,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_555])).

tff(c_2795,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2782,c_2178])).

tff(c_2817,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_74,c_2795])).

tff(c_2818,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_555])).

tff(c_6160,plain,(
    ! [A_353,D_351,C_350,B_354,F_352,E_355] :
      ( k1_partfun1(A_353,B_354,C_350,D_351,E_355,F_352) = k5_relat_1(E_355,F_352)
      | ~ m1_subset_1(F_352,k1_zfmisc_1(k2_zfmisc_1(C_350,D_351)))
      | ~ v1_funct_1(F_352)
      | ~ m1_subset_1(E_355,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354)))
      | ~ v1_funct_1(E_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_6170,plain,(
    ! [A_353,B_354,E_355] :
      ( k1_partfun1(A_353,B_354,'#skF_2','#skF_1',E_355,'#skF_4') = k5_relat_1(E_355,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_355,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354)))
      | ~ v1_funct_1(E_355) ) ),
    inference(resolution,[status(thm)],[c_74,c_6160])).

tff(c_6357,plain,(
    ! [A_368,B_369,E_370] :
      ( k1_partfun1(A_368,B_369,'#skF_2','#skF_1',E_370,'#skF_4') = k5_relat_1(E_370,'#skF_4')
      | ~ m1_subset_1(E_370,k1_zfmisc_1(k2_zfmisc_1(A_368,B_369)))
      | ~ v1_funct_1(E_370) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_6170])).

tff(c_6372,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_6357])).

tff(c_6384,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2818,c_6372])).

tff(c_421,plain,(
    ! [A_4,B_5,C_101] :
      ( k5_relat_1(k6_partfun1(A_4),k5_relat_1(B_5,C_101)) = k5_relat_1(B_5,C_101)
      | ~ v1_relat_1(C_101)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_415])).

tff(c_6394,plain,(
    ! [A_4] :
      ( k5_relat_1(k6_partfun1(A_4),k6_partfun1('#skF_1')) = k5_relat_1('#skF_3','#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v4_relat_1('#skF_3',A_4)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6384,c_421])).

tff(c_6834,plain,(
    ! [A_380] :
      ( k5_relat_1(k6_partfun1(A_380),k6_partfun1('#skF_1')) = k6_partfun1('#skF_1')
      | ~ v4_relat_1('#skF_3',A_380) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_134,c_6384,c_6394])).

tff(c_5870,plain,(
    ! [C_16] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),C_16) = k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),C_16))
      | ~ v1_relat_1(C_16)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5856,c_14])).

tff(c_5884,plain,(
    ! [C_16] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),C_16) = k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),C_16))
      | ~ v1_relat_1(C_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_3028,c_5870])).

tff(c_6845,plain,
    ( k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1'))) = k6_partfun1('#skF_1')
    | ~ v1_relat_1(k6_partfun1('#skF_1'))
    | ~ v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6834,c_5884])).

tff(c_6874,plain,(
    k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1'))) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_128,c_6845])).

tff(c_7552,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7546,c_6874])).

tff(c_7575,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_84,c_68,c_3028,c_5856,c_7552])).

tff(c_7587,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_7575])).

tff(c_7590,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_7587])).

tff(c_7594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_175,c_7590])).

tff(c_7596,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_7575])).

tff(c_30,plain,(
    ! [A_25] :
      ( k5_relat_1(k2_funct_1(A_25),A_25) = k6_relat_1(k2_relat_1(A_25))
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_486,plain,(
    ! [A_105] :
      ( k5_relat_1(k2_funct_1(A_105),A_105) = k6_partfun1(k2_relat_1(A_105))
      | ~ v2_funct_1(A_105)
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_30])).

tff(c_8773,plain,(
    ! [A_417,C_418] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_417)),C_418) = k5_relat_1(k2_funct_1(A_417),k5_relat_1(A_417,C_418))
      | ~ v1_relat_1(C_418)
      | ~ v1_relat_1(A_417)
      | ~ v1_relat_1(k2_funct_1(A_417))
      | ~ v2_funct_1(A_417)
      | ~ v1_funct_1(A_417)
      | ~ v1_relat_1(A_417) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_14])).

tff(c_8938,plain,(
    ! [C_418] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_418)) = k5_relat_1(k6_partfun1('#skF_2'),C_418)
      | ~ v1_relat_1(C_418)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_8773])).

tff(c_13361,plain,(
    ! [C_530] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_530)) = k5_relat_1(k6_partfun1('#skF_2'),C_530)
      | ~ v1_relat_1(C_530) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_84,c_68,c_3028,c_131,c_8938])).

tff(c_13421,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6384,c_13361])).

tff(c_13477,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_13421])).

tff(c_6669,plain,(
    ! [A_377] :
      ( k9_relat_1(k2_funct_1(A_377),k2_relat_1(A_377)) = k2_relat_1(k2_funct_1(A_377))
      | ~ v1_relat_1(k2_funct_1(A_377))
      | ~ v2_funct_1(A_377)
      | ~ v1_funct_1(A_377)
      | ~ v1_relat_1(A_377) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_10])).

tff(c_6685,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_6669])).

tff(c_6692,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_84,c_68,c_3028,c_6685])).

tff(c_6696,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6692,c_24])).

tff(c_6703,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_84,c_68,c_312,c_6696])).

tff(c_6729,plain,(
    ! [A_19] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(A_19)) = k2_funct_1('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_19)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6703,c_87])).

tff(c_6755,plain,(
    ! [A_19] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(A_19)) = k2_funct_1('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3028,c_6729])).

tff(c_13500,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_13477,c_6755])).

tff(c_13526,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7596,c_13500])).

tff(c_13568,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13526,c_184])).

tff(c_13591,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_176,c_13568])).

tff(c_13593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_13591])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.56/4.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.62/4.08  
% 11.62/4.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.62/4.08  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.62/4.08  
% 11.62/4.08  %Foreground sorts:
% 11.62/4.08  
% 11.62/4.08  
% 11.62/4.08  %Background operators:
% 11.62/4.08  
% 11.62/4.08  
% 11.62/4.08  %Foreground operators:
% 11.62/4.08  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.62/4.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.62/4.08  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.62/4.08  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.62/4.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.62/4.08  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 11.62/4.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.62/4.08  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.62/4.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.62/4.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.62/4.08  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.62/4.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.62/4.08  tff('#skF_2', type, '#skF_2': $i).
% 11.62/4.08  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.62/4.08  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 11.62/4.08  tff('#skF_3', type, '#skF_3': $i).
% 11.62/4.08  tff('#skF_1', type, '#skF_1': $i).
% 11.62/4.08  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.62/4.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.62/4.08  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 11.62/4.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.62/4.08  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 11.62/4.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.62/4.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.62/4.08  tff('#skF_4', type, '#skF_4': $i).
% 11.62/4.08  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.62/4.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.62/4.08  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.62/4.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.62/4.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.62/4.08  
% 11.62/4.10  tff(f_188, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 11.62/4.10  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.62/4.10  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.62/4.10  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.62/4.10  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 11.62/4.10  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 11.62/4.10  tff(f_152, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 11.62/4.10  tff(f_106, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 11.62/4.10  tff(f_140, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 11.62/4.10  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.62/4.10  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 11.62/4.10  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 11.62/4.10  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 11.62/4.10  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 11.62/4.10  tff(f_162, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 11.62/4.10  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 11.62/4.10  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 11.62/4.10  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 11.62/4.10  tff(f_136, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 11.62/4.10  tff(f_124, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 11.62/4.10  tff(f_150, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 11.62/4.10  tff(c_62, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_188])).
% 11.62/4.10  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.62/4.10  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 11.62/4.10  tff(c_116, plain, (![B_60, A_61]: (v1_relat_1(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.62/4.10  tff(c_125, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_74, c_116])).
% 11.62/4.10  tff(c_134, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_125])).
% 11.62/4.10  tff(c_164, plain, (![C_71, A_72, B_73]: (v4_relat_1(C_71, A_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.62/4.10  tff(c_176, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_164])).
% 11.62/4.10  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 11.62/4.10  tff(c_122, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_80, c_116])).
% 11.62/4.10  tff(c_131, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_122])).
% 11.62/4.10  tff(c_175, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_80, c_164])).
% 11.62/4.10  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.62/4.10  tff(c_84, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 11.62/4.10  tff(c_68, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 11.62/4.10  tff(c_22, plain, (![A_21]: (v1_relat_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.62/4.10  tff(c_54, plain, (![A_49]: (k6_relat_1(A_49)=k6_partfun1(A_49))), inference(cnfTransformation, [status(thm)], [f_152])).
% 11.62/4.10  tff(c_32, plain, (![A_25]: (k5_relat_1(A_25, k2_funct_1(A_25))=k6_relat_1(k1_relat_1(A_25)) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.62/4.10  tff(c_85, plain, (![A_25]: (k5_relat_1(A_25, k2_funct_1(A_25))=k6_partfun1(k1_relat_1(A_25)) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_32])).
% 11.62/4.10  tff(c_50, plain, (![A_42]: (m1_subset_1(k6_partfun1(A_42), k1_zfmisc_1(k2_zfmisc_1(A_42, A_42))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 11.62/4.10  tff(c_119, plain, (![A_42]: (v1_relat_1(k6_partfun1(A_42)) | ~v1_relat_1(k2_zfmisc_1(A_42, A_42)))), inference(resolution, [status(thm)], [c_50, c_116])).
% 11.62/4.10  tff(c_128, plain, (![A_42]: (v1_relat_1(k6_partfun1(A_42)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_119])).
% 11.62/4.10  tff(c_72, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_188])).
% 11.62/4.10  tff(c_248, plain, (![A_89, B_90, C_91]: (k2_relset_1(A_89, B_90, C_91)=k2_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 11.62/4.10  tff(c_254, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_248])).
% 11.62/4.10  tff(c_260, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_254])).
% 11.62/4.10  tff(c_194, plain, (![A_81]: (k1_relat_1(k2_funct_1(A_81))=k2_relat_1(A_81) | ~v2_funct_1(A_81) | ~v1_funct_1(A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.62/4.10  tff(c_10, plain, (![A_8]: (k9_relat_1(A_8, k1_relat_1(A_8))=k2_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.62/4.10  tff(c_926, plain, (![A_154]: (k9_relat_1(k2_funct_1(A_154), k2_relat_1(A_154))=k2_relat_1(k2_funct_1(A_154)) | ~v1_relat_1(k2_funct_1(A_154)) | ~v2_funct_1(A_154) | ~v1_funct_1(A_154) | ~v1_relat_1(A_154))), inference(superposition, [status(thm), theory('equality')], [c_194, c_10])).
% 11.62/4.10  tff(c_942, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_260, c_926])).
% 11.62/4.10  tff(c_949, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_84, c_68, c_942])).
% 11.62/4.10  tff(c_950, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_949])).
% 11.62/4.10  tff(c_953, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_950])).
% 11.62/4.10  tff(c_957, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_84, c_953])).
% 11.62/4.10  tff(c_959, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_949])).
% 11.62/4.10  tff(c_28, plain, (![A_24]: (k1_relat_1(k2_funct_1(A_24))=k2_relat_1(A_24) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.62/4.10  tff(c_20, plain, (![A_21]: (v1_funct_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.62/4.10  tff(c_12, plain, (![A_9]: (k10_relat_1(A_9, k2_relat_1(A_9))=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.62/4.10  tff(c_302, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_260, c_12])).
% 11.62/4.10  tff(c_312, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_302])).
% 11.62/4.10  tff(c_958, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_949])).
% 11.62/4.10  tff(c_24, plain, (![B_23, A_22]: (k9_relat_1(k2_funct_1(B_23), A_22)=k10_relat_1(B_23, A_22) | ~v2_funct_1(B_23) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.62/4.10  tff(c_985, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_958, c_24])).
% 11.62/4.10  tff(c_992, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_84, c_68, c_312, c_985])).
% 11.62/4.10  tff(c_262, plain, (![A_92]: (m1_subset_1(A_92, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_92), k2_relat_1(A_92)))) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_162])).
% 11.62/4.10  tff(c_34, plain, (![C_28, B_27, A_26]: (v5_relat_1(C_28, B_27) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.62/4.10  tff(c_286, plain, (![A_92]: (v5_relat_1(A_92, k2_relat_1(A_92)) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(resolution, [status(thm)], [c_262, c_34])).
% 11.62/4.10  tff(c_1009, plain, (v5_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_992, c_286])).
% 11.62/4.10  tff(c_1037, plain, (v5_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_959, c_1009])).
% 11.62/4.10  tff(c_1121, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1037])).
% 11.62/4.10  tff(c_1124, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_1121])).
% 11.62/4.10  tff(c_1128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_84, c_1124])).
% 11.62/4.10  tff(c_1130, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1037])).
% 11.62/4.10  tff(c_56, plain, (![A_50]: (m1_subset_1(A_50, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_50), k2_relat_1(A_50)))) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_162])).
% 11.62/4.10  tff(c_1012, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_992, c_56])).
% 11.62/4.10  tff(c_1039, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_959, c_1012])).
% 11.62/4.10  tff(c_1990, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1130, c_1039])).
% 11.62/4.10  tff(c_36, plain, (![C_28, A_26, B_27]: (v4_relat_1(C_28, A_26) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.62/4.10  tff(c_2050, plain, (v4_relat_1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_1990, c_36])).
% 11.62/4.10  tff(c_2063, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_2050])).
% 11.62/4.10  tff(c_2068, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_84, c_68, c_260, c_2063])).
% 11.62/4.10  tff(c_209, plain, (![A_81, A_4]: (r1_tarski(k2_relat_1(A_81), A_4) | ~v4_relat_1(k2_funct_1(A_81), A_4) | ~v1_relat_1(k2_funct_1(A_81)) | ~v2_funct_1(A_81) | ~v1_funct_1(A_81) | ~v1_relat_1(A_81))), inference(superposition, [status(thm), theory('equality')], [c_194, c_6])).
% 11.62/4.10  tff(c_2123, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2068, c_209])).
% 11.62/4.10  tff(c_2126, plain, (r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_84, c_68, c_959, c_260, c_2123])).
% 11.62/4.10  tff(c_18, plain, (![B_20, A_19]: (k5_relat_1(B_20, k6_relat_1(A_19))=B_20 | ~r1_tarski(k2_relat_1(B_20), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.62/4.10  tff(c_87, plain, (![B_20, A_19]: (k5_relat_1(B_20, k6_partfun1(A_19))=B_20 | ~r1_tarski(k2_relat_1(B_20), A_19) | ~v1_relat_1(B_20))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_18])).
% 11.62/4.10  tff(c_296, plain, (![A_19]: (k5_relat_1('#skF_3', k6_partfun1(A_19))='#skF_3' | ~r1_tarski('#skF_2', A_19) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_260, c_87])).
% 11.62/4.10  tff(c_308, plain, (![A_19]: (k5_relat_1('#skF_3', k6_partfun1(A_19))='#skF_3' | ~r1_tarski('#skF_2', A_19))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_296])).
% 11.62/4.10  tff(c_16, plain, (![A_17, B_18]: (k5_relat_1(k6_relat_1(A_17), B_18)=B_18 | ~r1_tarski(k1_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.62/4.10  tff(c_180, plain, (![A_77, B_78]: (k5_relat_1(k6_partfun1(A_77), B_78)=B_78 | ~r1_tarski(k1_relat_1(B_78), A_77) | ~v1_relat_1(B_78))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_16])).
% 11.62/4.10  tff(c_184, plain, (![A_4, B_5]: (k5_relat_1(k6_partfun1(A_4), B_5)=B_5 | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_180])).
% 11.62/4.10  tff(c_397, plain, (![A_99, B_100, C_101]: (k5_relat_1(k5_relat_1(A_99, B_100), C_101)=k5_relat_1(A_99, k5_relat_1(B_100, C_101)) | ~v1_relat_1(C_101) | ~v1_relat_1(B_100) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.62/4.10  tff(c_415, plain, (![A_4, B_5, C_101]: (k5_relat_1(k6_partfun1(A_4), k5_relat_1(B_5, C_101))=k5_relat_1(B_5, C_101) | ~v1_relat_1(C_101) | ~v1_relat_1(B_5) | ~v1_relat_1(k6_partfun1(A_4)) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(superposition, [status(thm), theory('equality')], [c_184, c_397])).
% 11.62/4.10  tff(c_556, plain, (![A_112, B_113, C_114]: (k5_relat_1(k6_partfun1(A_112), k5_relat_1(B_113, C_114))=k5_relat_1(B_113, C_114) | ~v1_relat_1(C_114) | ~v4_relat_1(B_113, A_112) | ~v1_relat_1(B_113))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_415])).
% 11.62/4.10  tff(c_592, plain, (![A_112, A_19]: (k5_relat_1(k6_partfun1(A_112), '#skF_3')=k5_relat_1('#skF_3', k6_partfun1(A_19)) | ~v1_relat_1(k6_partfun1(A_19)) | ~v4_relat_1('#skF_3', A_112) | ~v1_relat_1('#skF_3') | ~r1_tarski('#skF_2', A_19))), inference(superposition, [status(thm), theory('equality')], [c_308, c_556])).
% 11.62/4.10  tff(c_617, plain, (![A_115, A_116]: (k5_relat_1(k6_partfun1(A_115), '#skF_3')=k5_relat_1('#skF_3', k6_partfun1(A_116)) | ~v4_relat_1('#skF_3', A_115) | ~r1_tarski('#skF_2', A_116))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_128, c_592])).
% 11.62/4.10  tff(c_641, plain, (![A_115, A_116]: (k5_relat_1(k6_partfun1(A_115), '#skF_3')='#skF_3' | ~r1_tarski('#skF_2', A_116) | ~v4_relat_1('#skF_3', A_115) | ~r1_tarski('#skF_2', A_116))), inference(superposition, [status(thm), theory('equality')], [c_617, c_308])).
% 11.62/4.10  tff(c_672, plain, (![A_116]: (~r1_tarski('#skF_2', A_116) | ~r1_tarski('#skF_2', A_116))), inference(splitLeft, [status(thm)], [c_641])).
% 11.62/4.10  tff(c_2128, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_2126, c_672])).
% 11.62/4.10  tff(c_2132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2126, c_2128])).
% 11.62/4.10  tff(c_2134, plain, (![A_208]: (k5_relat_1(k6_partfun1(A_208), '#skF_3')='#skF_3' | ~v4_relat_1('#skF_3', A_208))), inference(splitRight, [status(thm)], [c_641])).
% 11.62/4.10  tff(c_14, plain, (![A_10, B_14, C_16]: (k5_relat_1(k5_relat_1(A_10, B_14), C_16)=k5_relat_1(A_10, k5_relat_1(B_14, C_16)) | ~v1_relat_1(C_16) | ~v1_relat_1(B_14) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.62/4.10  tff(c_2149, plain, (![A_208, C_16]: (k5_relat_1(k6_partfun1(A_208), k5_relat_1('#skF_3', C_16))=k5_relat_1('#skF_3', C_16) | ~v1_relat_1(C_16) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_partfun1(A_208)) | ~v4_relat_1('#skF_3', A_208))), inference(superposition, [status(thm), theory('equality')], [c_2134, c_14])).
% 11.62/4.10  tff(c_2910, plain, (![A_254, C_255]: (k5_relat_1(k6_partfun1(A_254), k5_relat_1('#skF_3', C_255))=k5_relat_1('#skF_3', C_255) | ~v1_relat_1(C_255) | ~v4_relat_1('#skF_3', A_254))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_131, c_2149])).
% 11.62/4.10  tff(c_2951, plain, (![A_254]: (k5_relat_1(k6_partfun1(A_254), k6_partfun1(k1_relat_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v4_relat_1('#skF_3', A_254) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_85, c_2910])).
% 11.62/4.10  tff(c_2980, plain, (![A_254]: (k5_relat_1(k6_partfun1(A_254), k6_partfun1(k1_relat_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v4_relat_1('#skF_3', A_254))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_84, c_68, c_2951])).
% 11.62/4.10  tff(c_2997, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2980])).
% 11.62/4.10  tff(c_3022, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_2997])).
% 11.62/4.10  tff(c_3026, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_84, c_3022])).
% 11.62/4.10  tff(c_3028, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2980])).
% 11.62/4.10  tff(c_293, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_260, c_56])).
% 11.62/4.10  tff(c_306, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_84, c_293])).
% 11.62/4.10  tff(c_339, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_306, c_36])).
% 11.62/4.10  tff(c_174, plain, (![A_42]: (v4_relat_1(k6_partfun1(A_42), A_42))), inference(resolution, [status(thm)], [c_50, c_164])).
% 11.62/4.10  tff(c_3029, plain, (![A_264]: (k5_relat_1(k6_partfun1(A_264), k6_partfun1(k1_relat_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v4_relat_1('#skF_3', A_264))), inference(splitRight, [status(thm)], [c_2980])).
% 11.62/4.10  tff(c_3051, plain, (![A_4]: (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | ~v4_relat_1('#skF_3', A_4) | ~v4_relat_1(k6_partfun1(k1_relat_1('#skF_3')), A_4) | ~v1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_184, c_3029])).
% 11.62/4.10  tff(c_3063, plain, (![A_4]: (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | ~v4_relat_1('#skF_3', A_4) | ~v4_relat_1(k6_partfun1(k1_relat_1('#skF_3')), A_4))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_3051])).
% 11.62/4.10  tff(c_5840, plain, (![A_338]: (~v4_relat_1('#skF_3', A_338) | ~v4_relat_1(k6_partfun1(k1_relat_1('#skF_3')), A_338))), inference(splitLeft, [status(thm)], [c_3063])).
% 11.62/4.10  tff(c_5848, plain, (~v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_174, c_5840])).
% 11.62/4.10  tff(c_5855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_339, c_5848])).
% 11.62/4.10  tff(c_5856, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3063])).
% 11.62/4.10  tff(c_230, plain, (![A_88]: (k2_relat_1(k2_funct_1(A_88))=k1_relat_1(A_88) | ~v2_funct_1(A_88) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.62/4.10  tff(c_7546, plain, (![A_390, A_391]: (k5_relat_1(k2_funct_1(A_390), k6_partfun1(A_391))=k2_funct_1(A_390) | ~r1_tarski(k1_relat_1(A_390), A_391) | ~v1_relat_1(k2_funct_1(A_390)) | ~v2_funct_1(A_390) | ~v1_funct_1(A_390) | ~v1_relat_1(A_390))), inference(superposition, [status(thm), theory('equality')], [c_230, c_87])).
% 11.62/4.10  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 11.62/4.10  tff(c_2782, plain, (![B_248, C_249, A_246, D_247, F_245, E_250]: (m1_subset_1(k1_partfun1(A_246, B_248, C_249, D_247, E_250, F_245), k1_zfmisc_1(k2_zfmisc_1(A_246, D_247))) | ~m1_subset_1(F_245, k1_zfmisc_1(k2_zfmisc_1(C_249, D_247))) | ~v1_funct_1(F_245) | ~m1_subset_1(E_250, k1_zfmisc_1(k2_zfmisc_1(A_246, B_248))) | ~v1_funct_1(E_250))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.62/4.11  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 11.62/4.11  tff(c_522, plain, (![D_108, C_109, A_110, B_111]: (D_108=C_109 | ~r2_relset_1(A_110, B_111, C_109, D_108) | ~m1_subset_1(D_108, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.62/4.11  tff(c_534, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_522])).
% 11.62/4.11  tff(c_555, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_534])).
% 11.62/4.11  tff(c_2178, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_555])).
% 11.62/4.11  tff(c_2795, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2782, c_2178])).
% 11.62/4.11  tff(c_2817, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_74, c_2795])).
% 11.62/4.11  tff(c_2818, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_555])).
% 11.62/4.11  tff(c_6160, plain, (![A_353, D_351, C_350, B_354, F_352, E_355]: (k1_partfun1(A_353, B_354, C_350, D_351, E_355, F_352)=k5_relat_1(E_355, F_352) | ~m1_subset_1(F_352, k1_zfmisc_1(k2_zfmisc_1(C_350, D_351))) | ~v1_funct_1(F_352) | ~m1_subset_1(E_355, k1_zfmisc_1(k2_zfmisc_1(A_353, B_354))) | ~v1_funct_1(E_355))), inference(cnfTransformation, [status(thm)], [f_150])).
% 11.62/4.11  tff(c_6170, plain, (![A_353, B_354, E_355]: (k1_partfun1(A_353, B_354, '#skF_2', '#skF_1', E_355, '#skF_4')=k5_relat_1(E_355, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_355, k1_zfmisc_1(k2_zfmisc_1(A_353, B_354))) | ~v1_funct_1(E_355))), inference(resolution, [status(thm)], [c_74, c_6160])).
% 11.62/4.11  tff(c_6357, plain, (![A_368, B_369, E_370]: (k1_partfun1(A_368, B_369, '#skF_2', '#skF_1', E_370, '#skF_4')=k5_relat_1(E_370, '#skF_4') | ~m1_subset_1(E_370, k1_zfmisc_1(k2_zfmisc_1(A_368, B_369))) | ~v1_funct_1(E_370))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_6170])).
% 11.62/4.11  tff(c_6372, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_6357])).
% 11.62/4.11  tff(c_6384, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2818, c_6372])).
% 11.62/4.11  tff(c_421, plain, (![A_4, B_5, C_101]: (k5_relat_1(k6_partfun1(A_4), k5_relat_1(B_5, C_101))=k5_relat_1(B_5, C_101) | ~v1_relat_1(C_101) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_415])).
% 11.62/4.11  tff(c_6394, plain, (![A_4]: (k5_relat_1(k6_partfun1(A_4), k6_partfun1('#skF_1'))=k5_relat_1('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~v4_relat_1('#skF_3', A_4) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6384, c_421])).
% 11.62/4.11  tff(c_6834, plain, (![A_380]: (k5_relat_1(k6_partfun1(A_380), k6_partfun1('#skF_1'))=k6_partfun1('#skF_1') | ~v4_relat_1('#skF_3', A_380))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_134, c_6384, c_6394])).
% 11.62/4.11  tff(c_5870, plain, (![C_16]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), C_16)=k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), C_16)) | ~v1_relat_1(C_16) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5856, c_14])).
% 11.62/4.11  tff(c_5884, plain, (![C_16]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), C_16)=k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), C_16)) | ~v1_relat_1(C_16))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_3028, c_5870])).
% 11.62/4.11  tff(c_6845, plain, (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1')))=k6_partfun1('#skF_1') | ~v1_relat_1(k6_partfun1('#skF_1')) | ~v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6834, c_5884])).
% 11.62/4.11  tff(c_6874, plain, (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1')))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_128, c_6845])).
% 11.62/4.11  tff(c_7552, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7546, c_6874])).
% 11.62/4.11  tff(c_7575, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_84, c_68, c_3028, c_5856, c_7552])).
% 11.62/4.11  tff(c_7587, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_7575])).
% 11.62/4.11  tff(c_7590, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_7587])).
% 11.62/4.11  tff(c_7594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_175, c_7590])).
% 11.62/4.11  tff(c_7596, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_7575])).
% 11.62/4.11  tff(c_30, plain, (![A_25]: (k5_relat_1(k2_funct_1(A_25), A_25)=k6_relat_1(k2_relat_1(A_25)) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.62/4.11  tff(c_486, plain, (![A_105]: (k5_relat_1(k2_funct_1(A_105), A_105)=k6_partfun1(k2_relat_1(A_105)) | ~v2_funct_1(A_105) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_30])).
% 11.62/4.11  tff(c_8773, plain, (![A_417, C_418]: (k5_relat_1(k6_partfun1(k2_relat_1(A_417)), C_418)=k5_relat_1(k2_funct_1(A_417), k5_relat_1(A_417, C_418)) | ~v1_relat_1(C_418) | ~v1_relat_1(A_417) | ~v1_relat_1(k2_funct_1(A_417)) | ~v2_funct_1(A_417) | ~v1_funct_1(A_417) | ~v1_relat_1(A_417))), inference(superposition, [status(thm), theory('equality')], [c_486, c_14])).
% 11.62/4.11  tff(c_8938, plain, (![C_418]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_418))=k5_relat_1(k6_partfun1('#skF_2'), C_418) | ~v1_relat_1(C_418) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_260, c_8773])).
% 11.62/4.11  tff(c_13361, plain, (![C_530]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_530))=k5_relat_1(k6_partfun1('#skF_2'), C_530) | ~v1_relat_1(C_530))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_84, c_68, c_3028, c_131, c_8938])).
% 11.62/4.11  tff(c_13421, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6384, c_13361])).
% 11.62/4.11  tff(c_13477, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_13421])).
% 11.62/4.11  tff(c_6669, plain, (![A_377]: (k9_relat_1(k2_funct_1(A_377), k2_relat_1(A_377))=k2_relat_1(k2_funct_1(A_377)) | ~v1_relat_1(k2_funct_1(A_377)) | ~v2_funct_1(A_377) | ~v1_funct_1(A_377) | ~v1_relat_1(A_377))), inference(superposition, [status(thm), theory('equality')], [c_194, c_10])).
% 11.62/4.11  tff(c_6685, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_260, c_6669])).
% 11.62/4.11  tff(c_6692, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_84, c_68, c_3028, c_6685])).
% 11.62/4.11  tff(c_6696, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6692, c_24])).
% 11.62/4.11  tff(c_6703, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_84, c_68, c_312, c_6696])).
% 11.62/4.11  tff(c_6729, plain, (![A_19]: (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(A_19))=k2_funct_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), A_19) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6703, c_87])).
% 11.62/4.11  tff(c_6755, plain, (![A_19]: (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(A_19))=k2_funct_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), A_19))), inference(demodulation, [status(thm), theory('equality')], [c_3028, c_6729])).
% 11.62/4.11  tff(c_13500, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_13477, c_6755])).
% 11.62/4.11  tff(c_13526, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7596, c_13500])).
% 11.62/4.11  tff(c_13568, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13526, c_184])).
% 11.62/4.11  tff(c_13591, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_176, c_13568])).
% 11.62/4.11  tff(c_13593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_13591])).
% 11.62/4.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.62/4.11  
% 11.62/4.11  Inference rules
% 11.62/4.11  ----------------------
% 11.62/4.11  #Ref     : 0
% 11.62/4.11  #Sup     : 2907
% 11.62/4.11  #Fact    : 0
% 11.62/4.11  #Define  : 0
% 11.62/4.11  #Split   : 23
% 11.62/4.11  #Chain   : 0
% 11.62/4.11  #Close   : 0
% 11.62/4.11  
% 11.62/4.11  Ordering : KBO
% 11.62/4.11  
% 11.62/4.11  Simplification rules
% 11.62/4.11  ----------------------
% 11.62/4.11  #Subsume      : 242
% 11.62/4.11  #Demod        : 3582
% 11.62/4.11  #Tautology    : 830
% 11.62/4.11  #SimpNegUnit  : 1
% 11.62/4.11  #BackRed      : 43
% 11.62/4.11  
% 11.62/4.11  #Partial instantiations: 0
% 11.62/4.11  #Strategies tried      : 1
% 11.62/4.11  
% 11.62/4.11  Timing (in seconds)
% 11.62/4.11  ----------------------
% 11.62/4.11  Preprocessing        : 0.39
% 11.62/4.11  Parsing              : 0.20
% 11.62/4.11  CNF conversion       : 0.03
% 11.62/4.11  Main loop            : 2.92
% 11.62/4.11  Inferencing          : 0.85
% 11.62/4.11  Reduction            : 1.34
% 11.62/4.11  Demodulation         : 1.08
% 11.62/4.11  BG Simplification    : 0.09
% 11.62/4.11  Subsumption          : 0.48
% 11.62/4.11  Abstraction          : 0.11
% 11.62/4.11  MUC search           : 0.00
% 11.62/4.11  Cooper               : 0.00
% 11.62/4.11  Total                : 3.36
% 11.62/4.11  Index Insertion      : 0.00
% 11.62/4.11  Index Deletion       : 0.00
% 11.62/4.11  Index Matching       : 0.00
% 11.62/4.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
