%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:15 EST 2020

% Result     : Theorem 10.26s
% Output     : CNFRefutation 10.59s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 953 expanded)
%              Number of leaves         :   45 ( 344 expanded)
%              Depth                    :   22
%              Number of atoms          :  358 (2762 expanded)
%              Number of equality atoms :   87 ( 710 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_162,negated_conjecture,(
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

tff(f_120,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_96,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_136,axiom,(
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

tff(f_118,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_48,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_91,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_91])).

tff(c_109,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_100])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_40,plain,(
    ! [A_45] : k6_relat_1(A_45) = k6_partfun1(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_20,plain,(
    ! [A_21] :
      ( k5_relat_1(A_21,k2_funct_1(A_21)) = k6_relat_1(k1_relat_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_72,plain,(
    ! [A_21] :
      ( k5_relat_1(A_21,k2_funct_1(A_21)) = k6_partfun1(k1_relat_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_20])).

tff(c_32,plain,(
    ! [A_32] : m1_subset_1(k6_relat_1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_71,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32])).

tff(c_94,plain,(
    ! [A_32] :
      ( v1_relat_1(k6_partfun1(A_32))
      | ~ v1_relat_1(k2_zfmisc_1(A_32,A_32)) ) ),
    inference(resolution,[status(thm)],[c_71,c_91])).

tff(c_103,plain,(
    ! [A_32] : v1_relat_1(k6_partfun1(A_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_94])).

tff(c_110,plain,(
    ! [C_56,B_57,A_58] :
      ( v5_relat_1(C_56,B_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_58,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_122,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_110])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_206,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_relset_1(A_80,B_81,C_82) = k2_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_215,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_206])).

tff(c_219,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_215])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_226,plain,(
    ! [A_4] :
      ( r1_tarski('#skF_2',A_4)
      | ~ v5_relat_1('#skF_3',A_4)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_6])).

tff(c_244,plain,(
    ! [A_84] :
      ( r1_tarski('#skF_2',A_84)
      | ~ v5_relat_1('#skF_3',A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_226])).

tff(c_252,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_122,c_244])).

tff(c_126,plain,(
    ! [C_63,A_64,B_65] :
      ( v4_relat_1(C_63,A_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_138,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_126])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_148,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_138,c_10])).

tff(c_151,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_148])).

tff(c_14,plain,(
    ! [B_18,A_17] :
      ( k5_relat_1(B_18,k6_relat_1(A_17)) = B_18
      | ~ r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_75,plain,(
    ! [B_18,A_17] :
      ( k5_relat_1(B_18,k6_partfun1(A_17)) = B_18
      | ~ r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_223,plain,(
    ! [A_17] :
      ( k5_relat_1('#skF_3',k6_partfun1(A_17)) = '#skF_3'
      | ~ r1_tarski('#skF_2',A_17)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_75])).

tff(c_233,plain,(
    ! [A_17] :
      ( k5_relat_1('#skF_3',k6_partfun1(A_17)) = '#skF_3'
      | ~ r1_tarski('#skF_2',A_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_223])).

tff(c_16,plain,(
    ! [A_19,B_20] :
      ( k5_relat_1(k6_relat_1(A_19),B_20) = k7_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_74,plain,(
    ! [A_19,B_20] :
      ( k5_relat_1(k6_partfun1(A_19),B_20) = k7_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16])).

tff(c_326,plain,(
    ! [A_90,B_91,C_92] :
      ( k5_relat_1(k5_relat_1(A_90,B_91),C_92) = k5_relat_1(A_90,k5_relat_1(B_91,C_92))
      | ~ v1_relat_1(C_92)
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_358,plain,(
    ! [A_19,B_20,C_92] :
      ( k5_relat_1(k6_partfun1(A_19),k5_relat_1(B_20,C_92)) = k5_relat_1(k7_relat_1(B_20,A_19),C_92)
      | ~ v1_relat_1(C_92)
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(k6_partfun1(A_19))
      | ~ v1_relat_1(B_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_326])).

tff(c_438,plain,(
    ! [A_98,B_99,C_100] :
      ( k5_relat_1(k6_partfun1(A_98),k5_relat_1(B_99,C_100)) = k5_relat_1(k7_relat_1(B_99,A_98),C_100)
      | ~ v1_relat_1(C_100)
      | ~ v1_relat_1(B_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_358])).

tff(c_474,plain,(
    ! [A_98,A_17] :
      ( k5_relat_1(k7_relat_1('#skF_3',A_98),k6_partfun1(A_17)) = k5_relat_1(k6_partfun1(A_98),'#skF_3')
      | ~ v1_relat_1(k6_partfun1(A_17))
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski('#skF_2',A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_438])).

tff(c_525,plain,(
    ! [A_105,A_106] :
      ( k5_relat_1(k7_relat_1('#skF_3',A_105),k6_partfun1(A_106)) = k5_relat_1(k6_partfun1(A_105),'#skF_3')
      | ~ r1_tarski('#skF_2',A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_103,c_474])).

tff(c_554,plain,(
    ! [A_107] :
      ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = k5_relat_1('#skF_3',k6_partfun1(A_107))
      | ~ r1_tarski('#skF_2',A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_525])).

tff(c_200,plain,(
    ! [B_77,A_78] :
      ( k5_relat_1(B_77,k6_partfun1(A_78)) = B_77
      | ~ r1_tarski(k2_relat_1(B_77),A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_204,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_partfun1(A_4)) = B_5
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_200])).

tff(c_576,plain,(
    ! [A_107] :
      ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
      | ~ v5_relat_1('#skF_3',A_107)
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski('#skF_2',A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_204])).

tff(c_609,plain,(
    ! [A_107] :
      ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
      | ~ v5_relat_1('#skF_3',A_107)
      | ~ r1_tarski('#skF_2',A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_576])).

tff(c_619,plain,(
    ! [A_108] :
      ( ~ v5_relat_1('#skF_3',A_108)
      | ~ r1_tarski('#skF_2',A_108) ) ),
    inference(splitLeft,[status(thm)],[c_609])).

tff(c_625,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_122,c_619])).

tff(c_630,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_625])).

tff(c_631,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_609])).

tff(c_12,plain,(
    ! [A_10,B_14,C_16] :
      ( k5_relat_1(k5_relat_1(A_10,B_14),C_16) = k5_relat_1(A_10,k5_relat_1(B_14,C_16))
      | ~ v1_relat_1(C_16)
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_642,plain,(
    ! [C_16] :
      ( k5_relat_1(k6_partfun1('#skF_1'),k5_relat_1('#skF_3',C_16)) = k5_relat_1('#skF_3',C_16)
      | ~ v1_relat_1(C_16)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k6_partfun1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_631,c_12])).

tff(c_1710,plain,(
    ! [C_169] :
      ( k5_relat_1(k6_partfun1('#skF_1'),k5_relat_1('#skF_3',C_169)) = k5_relat_1('#skF_3',C_169)
      | ~ v1_relat_1(C_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_109,c_642])).

tff(c_1742,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k6_partfun1(k1_relat_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_1710])).

tff(c_1765,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k6_partfun1(k1_relat_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_70,c_54,c_1742])).

tff(c_1815,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1765])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_2419,plain,(
    ! [C_202,B_203,A_204] :
      ( m1_subset_1(k2_funct_1(C_202),k1_zfmisc_1(k2_zfmisc_1(B_203,A_204)))
      | k2_relset_1(A_204,B_203,C_202) != B_203
      | ~ v2_funct_1(C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_204,B_203)))
      | ~ v1_funct_2(C_202,A_204,B_203)
      | ~ v1_funct_1(C_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2444,plain,(
    ! [C_202,B_203,A_204] :
      ( v1_relat_1(k2_funct_1(C_202))
      | ~ v1_relat_1(k2_zfmisc_1(B_203,A_204))
      | k2_relset_1(A_204,B_203,C_202) != B_203
      | ~ v2_funct_1(C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_204,B_203)))
      | ~ v1_funct_2(C_202,A_204,B_203)
      | ~ v1_funct_1(C_202) ) ),
    inference(resolution,[status(thm)],[c_2419,c_2])).

tff(c_3565,plain,(
    ! [C_246,A_247,B_248] :
      ( v1_relat_1(k2_funct_1(C_246))
      | k2_relset_1(A_247,B_248,C_246) != B_248
      | ~ v2_funct_1(C_246)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248)))
      | ~ v1_funct_2(C_246,A_247,B_248)
      | ~ v1_funct_1(C_246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2444])).

tff(c_3589,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_3565])).

tff(c_3608,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_58,c_3589])).

tff(c_3610,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1815,c_3608])).

tff(c_3612,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1765])).

tff(c_4140,plain,(
    ! [C_278,B_279,A_280] :
      ( m1_subset_1(k2_funct_1(C_278),k1_zfmisc_1(k2_zfmisc_1(B_279,A_280)))
      | k2_relset_1(A_280,B_279,C_278) != B_279
      | ~ v2_funct_1(C_278)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_280,B_279)))
      | ~ v1_funct_2(C_278,A_280,B_279)
      | ~ v1_funct_1(C_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_22,plain,(
    ! [C_24,B_23,A_22] :
      ( v5_relat_1(C_24,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5703,plain,(
    ! [C_330,A_331,B_332] :
      ( v5_relat_1(k2_funct_1(C_330),A_331)
      | k2_relset_1(A_331,B_332,C_330) != B_332
      | ~ v2_funct_1(C_330)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(A_331,B_332)))
      | ~ v1_funct_2(C_330,A_331,B_332)
      | ~ v1_funct_1(C_330) ) ),
    inference(resolution,[status(thm)],[c_4140,c_22])).

tff(c_5730,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_5703])).

tff(c_5752,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_58,c_5730])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_97,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_91])).

tff(c_106,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_97])).

tff(c_137,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_126])).

tff(c_142,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_137,c_10])).

tff(c_145,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_142])).

tff(c_471,plain,(
    ! [B_5,A_98,A_4] :
      ( k5_relat_1(k7_relat_1(B_5,A_98),k6_partfun1(A_4)) = k5_relat_1(k6_partfun1(A_98),B_5)
      | ~ v1_relat_1(k6_partfun1(A_4))
      | ~ v1_relat_1(B_5)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_438])).

tff(c_4282,plain,(
    ! [B_286,A_287,A_288] :
      ( k5_relat_1(k7_relat_1(B_286,A_287),k6_partfun1(A_288)) = k5_relat_1(k6_partfun1(A_287),B_286)
      | ~ v5_relat_1(B_286,A_288)
      | ~ v1_relat_1(B_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_471])).

tff(c_4344,plain,(
    ! [A_288] :
      ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k5_relat_1('#skF_4',k6_partfun1(A_288))
      | ~ v5_relat_1('#skF_4',A_288)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_4282])).

tff(c_4393,plain,(
    ! [A_295] :
      ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k5_relat_1('#skF_4',k6_partfun1(A_295))
      | ~ v5_relat_1('#skF_4',A_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_4344])).

tff(c_4418,plain,(
    ! [A_295] :
      ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
      | ~ v5_relat_1('#skF_4',A_295)
      | ~ v1_relat_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_295) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4393,c_204])).

tff(c_4447,plain,(
    ! [A_295] :
      ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
      | ~ v5_relat_1('#skF_4',A_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_4418])).

tff(c_4455,plain,(
    ! [A_295] : ~ v5_relat_1('#skF_4',A_295) ),
    inference(splitLeft,[status(thm)],[c_4447])).

tff(c_121,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_110])).

tff(c_4457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4455,c_121])).

tff(c_4458,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4447])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1551,plain,(
    ! [C_155,F_157,D_156,A_153,E_158,B_154] :
      ( k1_partfun1(A_153,B_154,C_155,D_156,E_158,F_157) = k5_relat_1(E_158,F_157)
      | ~ m1_subset_1(F_157,k1_zfmisc_1(k2_zfmisc_1(C_155,D_156)))
      | ~ v1_funct_1(F_157)
      | ~ m1_subset_1(E_158,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154)))
      | ~ v1_funct_1(E_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1557,plain,(
    ! [A_153,B_154,E_158] :
      ( k1_partfun1(A_153,B_154,'#skF_2','#skF_1',E_158,'#skF_4') = k5_relat_1(E_158,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_158,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154)))
      | ~ v1_funct_1(E_158) ) ),
    inference(resolution,[status(thm)],[c_60,c_1551])).

tff(c_1603,plain,(
    ! [A_160,B_161,E_162] :
      ( k1_partfun1(A_160,B_161,'#skF_2','#skF_1',E_162,'#skF_4') = k5_relat_1(E_162,'#skF_4')
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161)))
      | ~ v1_funct_1(E_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1557])).

tff(c_1615,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1603])).

tff(c_1623,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1615])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_501,plain,(
    ! [D_101,C_102,A_103,B_104] :
      ( D_101 = C_102
      | ~ r2_relset_1(A_103,B_104,C_102,D_101)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_509,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_501])).

tff(c_524,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_509])).

tff(c_708,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_524])).

tff(c_1630,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1623,c_708])).

tff(c_1641,plain,(
    ! [A_163,C_165,F_166,E_164,D_167,B_168] :
      ( m1_subset_1(k1_partfun1(A_163,B_168,C_165,D_167,E_164,F_166),k1_zfmisc_1(k2_zfmisc_1(A_163,D_167)))
      | ~ m1_subset_1(F_166,k1_zfmisc_1(k2_zfmisc_1(C_165,D_167)))
      | ~ v1_funct_1(F_166)
      | ~ m1_subset_1(E_164,k1_zfmisc_1(k2_zfmisc_1(A_163,B_168)))
      | ~ v1_funct_1(E_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1677,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1623,c_1641])).

tff(c_1696,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_1677])).

tff(c_1699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1630,c_1696])).

tff(c_1700,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_524])).

tff(c_4376,plain,(
    ! [F_293,A_289,B_290,C_291,E_294,D_292] :
      ( k1_partfun1(A_289,B_290,C_291,D_292,E_294,F_293) = k5_relat_1(E_294,F_293)
      | ~ m1_subset_1(F_293,k1_zfmisc_1(k2_zfmisc_1(C_291,D_292)))
      | ~ v1_funct_1(F_293)
      | ~ m1_subset_1(E_294,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290)))
      | ~ v1_funct_1(E_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4382,plain,(
    ! [A_289,B_290,E_294] :
      ( k1_partfun1(A_289,B_290,'#skF_2','#skF_1',E_294,'#skF_4') = k5_relat_1(E_294,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_294,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290)))
      | ~ v1_funct_1(E_294) ) ),
    inference(resolution,[status(thm)],[c_60,c_4376])).

tff(c_4459,plain,(
    ! [A_296,B_297,E_298] :
      ( k1_partfun1(A_296,B_297,'#skF_2','#skF_1',E_298,'#skF_4') = k5_relat_1(E_298,'#skF_4')
      | ~ m1_subset_1(E_298,k1_zfmisc_1(k2_zfmisc_1(A_296,B_297)))
      | ~ v1_funct_1(E_298) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4382])).

tff(c_4471,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_4459])).

tff(c_4479,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1700,c_4471])).

tff(c_18,plain,(
    ! [A_21] :
      ( k5_relat_1(k2_funct_1(A_21),A_21) = k6_relat_1(k2_relat_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_73,plain,(
    ! [A_21] :
      ( k5_relat_1(k2_funct_1(A_21),A_21) = k6_partfun1(k2_relat_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18])).

tff(c_6413,plain,(
    ! [A_346,C_347] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_346)),C_347) = k5_relat_1(k2_funct_1(A_346),k5_relat_1(A_346,C_347))
      | ~ v1_relat_1(C_347)
      | ~ v1_relat_1(A_346)
      | ~ v1_relat_1(k2_funct_1(A_346))
      | ~ v2_funct_1(A_346)
      | ~ v1_funct_1(A_346)
      | ~ v1_relat_1(A_346) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_326])).

tff(c_6570,plain,(
    ! [C_347] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_347)) = k5_relat_1(k6_partfun1('#skF_2'),C_347)
      | ~ v1_relat_1(C_347)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_6413])).

tff(c_11041,plain,(
    ! [C_443] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_443)) = k5_relat_1(k6_partfun1('#skF_2'),C_443)
      | ~ v1_relat_1(C_443) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_70,c_54,c_3612,c_109,c_6570])).

tff(c_11119,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4479,c_11041])).

tff(c_11175,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_4458,c_11119])).

tff(c_11262,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11175,c_204])).

tff(c_11279,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3612,c_5752,c_11262])).

tff(c_11281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_11279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:39:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.26/3.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.26/3.76  
% 10.26/3.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.52/3.76  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.52/3.76  
% 10.52/3.76  %Foreground sorts:
% 10.52/3.76  
% 10.52/3.76  
% 10.52/3.76  %Background operators:
% 10.52/3.76  
% 10.52/3.76  
% 10.52/3.76  %Foreground operators:
% 10.52/3.76  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.52/3.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.52/3.76  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.52/3.76  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.52/3.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.52/3.76  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.52/3.76  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.52/3.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.52/3.76  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.52/3.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.52/3.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.52/3.76  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.52/3.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.52/3.76  tff('#skF_2', type, '#skF_2': $i).
% 10.52/3.76  tff('#skF_3', type, '#skF_3': $i).
% 10.52/3.76  tff('#skF_1', type, '#skF_1': $i).
% 10.52/3.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.52/3.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.52/3.76  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 10.52/3.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.52/3.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.52/3.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.52/3.76  tff('#skF_4', type, '#skF_4': $i).
% 10.52/3.76  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.52/3.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.52/3.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.52/3.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.52/3.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.52/3.76  
% 10.59/3.79  tff(f_162, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 10.59/3.79  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.59/3.79  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.59/3.79  tff(f_120, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.59/3.79  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 10.59/3.79  tff(f_96, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 10.59/3.79  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.59/3.79  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.59/3.79  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 10.59/3.79  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 10.59/3.79  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 10.59/3.79  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 10.59/3.79  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 10.59/3.79  tff(f_136, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 10.59/3.79  tff(f_118, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.59/3.79  tff(f_94, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.59/3.79  tff(f_108, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 10.59/3.79  tff(c_48, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.59/3.79  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.59/3.79  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.59/3.79  tff(c_91, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.59/3.79  tff(c_100, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_91])).
% 10.59/3.79  tff(c_109, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_100])).
% 10.59/3.79  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.59/3.79  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.59/3.79  tff(c_40, plain, (![A_45]: (k6_relat_1(A_45)=k6_partfun1(A_45))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.59/3.79  tff(c_20, plain, (![A_21]: (k5_relat_1(A_21, k2_funct_1(A_21))=k6_relat_1(k1_relat_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.59/3.79  tff(c_72, plain, (![A_21]: (k5_relat_1(A_21, k2_funct_1(A_21))=k6_partfun1(k1_relat_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_20])).
% 10.59/3.79  tff(c_32, plain, (![A_32]: (m1_subset_1(k6_relat_1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.59/3.79  tff(c_71, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32])).
% 10.59/3.79  tff(c_94, plain, (![A_32]: (v1_relat_1(k6_partfun1(A_32)) | ~v1_relat_1(k2_zfmisc_1(A_32, A_32)))), inference(resolution, [status(thm)], [c_71, c_91])).
% 10.59/3.79  tff(c_103, plain, (![A_32]: (v1_relat_1(k6_partfun1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_94])).
% 10.59/3.79  tff(c_110, plain, (![C_56, B_57, A_58]: (v5_relat_1(C_56, B_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_58, B_57))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.59/3.79  tff(c_122, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_110])).
% 10.59/3.79  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.59/3.79  tff(c_206, plain, (![A_80, B_81, C_82]: (k2_relset_1(A_80, B_81, C_82)=k2_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.59/3.79  tff(c_215, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_206])).
% 10.59/3.79  tff(c_219, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_215])).
% 10.59/3.79  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.59/3.79  tff(c_226, plain, (![A_4]: (r1_tarski('#skF_2', A_4) | ~v5_relat_1('#skF_3', A_4) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_219, c_6])).
% 10.59/3.79  tff(c_244, plain, (![A_84]: (r1_tarski('#skF_2', A_84) | ~v5_relat_1('#skF_3', A_84))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_226])).
% 10.59/3.79  tff(c_252, plain, (r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_122, c_244])).
% 10.59/3.79  tff(c_126, plain, (![C_63, A_64, B_65]: (v4_relat_1(C_63, A_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.59/3.79  tff(c_138, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_126])).
% 10.59/3.79  tff(c_10, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.59/3.79  tff(c_148, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_138, c_10])).
% 10.59/3.79  tff(c_151, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_148])).
% 10.59/3.79  tff(c_14, plain, (![B_18, A_17]: (k5_relat_1(B_18, k6_relat_1(A_17))=B_18 | ~r1_tarski(k2_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.59/3.79  tff(c_75, plain, (![B_18, A_17]: (k5_relat_1(B_18, k6_partfun1(A_17))=B_18 | ~r1_tarski(k2_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_14])).
% 10.59/3.79  tff(c_223, plain, (![A_17]: (k5_relat_1('#skF_3', k6_partfun1(A_17))='#skF_3' | ~r1_tarski('#skF_2', A_17) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_219, c_75])).
% 10.59/3.79  tff(c_233, plain, (![A_17]: (k5_relat_1('#skF_3', k6_partfun1(A_17))='#skF_3' | ~r1_tarski('#skF_2', A_17))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_223])).
% 10.59/3.79  tff(c_16, plain, (![A_19, B_20]: (k5_relat_1(k6_relat_1(A_19), B_20)=k7_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.59/3.79  tff(c_74, plain, (![A_19, B_20]: (k5_relat_1(k6_partfun1(A_19), B_20)=k7_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_16])).
% 10.59/3.79  tff(c_326, plain, (![A_90, B_91, C_92]: (k5_relat_1(k5_relat_1(A_90, B_91), C_92)=k5_relat_1(A_90, k5_relat_1(B_91, C_92)) | ~v1_relat_1(C_92) | ~v1_relat_1(B_91) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.59/3.79  tff(c_358, plain, (![A_19, B_20, C_92]: (k5_relat_1(k6_partfun1(A_19), k5_relat_1(B_20, C_92))=k5_relat_1(k7_relat_1(B_20, A_19), C_92) | ~v1_relat_1(C_92) | ~v1_relat_1(B_20) | ~v1_relat_1(k6_partfun1(A_19)) | ~v1_relat_1(B_20))), inference(superposition, [status(thm), theory('equality')], [c_74, c_326])).
% 10.59/3.79  tff(c_438, plain, (![A_98, B_99, C_100]: (k5_relat_1(k6_partfun1(A_98), k5_relat_1(B_99, C_100))=k5_relat_1(k7_relat_1(B_99, A_98), C_100) | ~v1_relat_1(C_100) | ~v1_relat_1(B_99))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_358])).
% 10.59/3.79  tff(c_474, plain, (![A_98, A_17]: (k5_relat_1(k7_relat_1('#skF_3', A_98), k6_partfun1(A_17))=k5_relat_1(k6_partfun1(A_98), '#skF_3') | ~v1_relat_1(k6_partfun1(A_17)) | ~v1_relat_1('#skF_3') | ~r1_tarski('#skF_2', A_17))), inference(superposition, [status(thm), theory('equality')], [c_233, c_438])).
% 10.59/3.79  tff(c_525, plain, (![A_105, A_106]: (k5_relat_1(k7_relat_1('#skF_3', A_105), k6_partfun1(A_106))=k5_relat_1(k6_partfun1(A_105), '#skF_3') | ~r1_tarski('#skF_2', A_106))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_103, c_474])).
% 10.59/3.79  tff(c_554, plain, (![A_107]: (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')=k5_relat_1('#skF_3', k6_partfun1(A_107)) | ~r1_tarski('#skF_2', A_107))), inference(superposition, [status(thm), theory('equality')], [c_151, c_525])).
% 10.59/3.79  tff(c_200, plain, (![B_77, A_78]: (k5_relat_1(B_77, k6_partfun1(A_78))=B_77 | ~r1_tarski(k2_relat_1(B_77), A_78) | ~v1_relat_1(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_14])).
% 10.59/3.79  tff(c_204, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_partfun1(A_4))=B_5 | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_200])).
% 10.59/3.79  tff(c_576, plain, (![A_107]: (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~v5_relat_1('#skF_3', A_107) | ~v1_relat_1('#skF_3') | ~r1_tarski('#skF_2', A_107))), inference(superposition, [status(thm), theory('equality')], [c_554, c_204])).
% 10.59/3.79  tff(c_609, plain, (![A_107]: (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~v5_relat_1('#skF_3', A_107) | ~r1_tarski('#skF_2', A_107))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_576])).
% 10.59/3.79  tff(c_619, plain, (![A_108]: (~v5_relat_1('#skF_3', A_108) | ~r1_tarski('#skF_2', A_108))), inference(splitLeft, [status(thm)], [c_609])).
% 10.59/3.79  tff(c_625, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_122, c_619])).
% 10.59/3.79  tff(c_630, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_252, c_625])).
% 10.59/3.79  tff(c_631, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_609])).
% 10.59/3.79  tff(c_12, plain, (![A_10, B_14, C_16]: (k5_relat_1(k5_relat_1(A_10, B_14), C_16)=k5_relat_1(A_10, k5_relat_1(B_14, C_16)) | ~v1_relat_1(C_16) | ~v1_relat_1(B_14) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.59/3.79  tff(c_642, plain, (![C_16]: (k5_relat_1(k6_partfun1('#skF_1'), k5_relat_1('#skF_3', C_16))=k5_relat_1('#skF_3', C_16) | ~v1_relat_1(C_16) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_partfun1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_631, c_12])).
% 10.59/3.79  tff(c_1710, plain, (![C_169]: (k5_relat_1(k6_partfun1('#skF_1'), k5_relat_1('#skF_3', C_169))=k5_relat_1('#skF_3', C_169) | ~v1_relat_1(C_169))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_109, c_642])).
% 10.59/3.79  tff(c_1742, plain, (k5_relat_1(k6_partfun1('#skF_1'), k6_partfun1(k1_relat_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_72, c_1710])).
% 10.59/3.79  tff(c_1765, plain, (k5_relat_1(k6_partfun1('#skF_1'), k6_partfun1(k1_relat_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_70, c_54, c_1742])).
% 10.59/3.79  tff(c_1815, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1765])).
% 10.59/3.79  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.59/3.79  tff(c_2419, plain, (![C_202, B_203, A_204]: (m1_subset_1(k2_funct_1(C_202), k1_zfmisc_1(k2_zfmisc_1(B_203, A_204))) | k2_relset_1(A_204, B_203, C_202)!=B_203 | ~v2_funct_1(C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_204, B_203))) | ~v1_funct_2(C_202, A_204, B_203) | ~v1_funct_1(C_202))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.59/3.79  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.59/3.79  tff(c_2444, plain, (![C_202, B_203, A_204]: (v1_relat_1(k2_funct_1(C_202)) | ~v1_relat_1(k2_zfmisc_1(B_203, A_204)) | k2_relset_1(A_204, B_203, C_202)!=B_203 | ~v2_funct_1(C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_204, B_203))) | ~v1_funct_2(C_202, A_204, B_203) | ~v1_funct_1(C_202))), inference(resolution, [status(thm)], [c_2419, c_2])).
% 10.59/3.79  tff(c_3565, plain, (![C_246, A_247, B_248]: (v1_relat_1(k2_funct_1(C_246)) | k2_relset_1(A_247, B_248, C_246)!=B_248 | ~v2_funct_1(C_246) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))) | ~v1_funct_2(C_246, A_247, B_248) | ~v1_funct_1(C_246))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2444])).
% 10.59/3.79  tff(c_3589, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_3565])).
% 10.59/3.79  tff(c_3608, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_58, c_3589])).
% 10.59/3.79  tff(c_3610, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1815, c_3608])).
% 10.59/3.79  tff(c_3612, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1765])).
% 10.59/3.79  tff(c_4140, plain, (![C_278, B_279, A_280]: (m1_subset_1(k2_funct_1(C_278), k1_zfmisc_1(k2_zfmisc_1(B_279, A_280))) | k2_relset_1(A_280, B_279, C_278)!=B_279 | ~v2_funct_1(C_278) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_280, B_279))) | ~v1_funct_2(C_278, A_280, B_279) | ~v1_funct_1(C_278))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.59/3.79  tff(c_22, plain, (![C_24, B_23, A_22]: (v5_relat_1(C_24, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.59/3.79  tff(c_5703, plain, (![C_330, A_331, B_332]: (v5_relat_1(k2_funct_1(C_330), A_331) | k2_relset_1(A_331, B_332, C_330)!=B_332 | ~v2_funct_1(C_330) | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(A_331, B_332))) | ~v1_funct_2(C_330, A_331, B_332) | ~v1_funct_1(C_330))), inference(resolution, [status(thm)], [c_4140, c_22])).
% 10.59/3.79  tff(c_5730, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_5703])).
% 10.59/3.79  tff(c_5752, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_58, c_5730])).
% 10.59/3.79  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.59/3.79  tff(c_97, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_91])).
% 10.59/3.79  tff(c_106, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_97])).
% 10.59/3.79  tff(c_137, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_126])).
% 10.59/3.79  tff(c_142, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_137, c_10])).
% 10.59/3.79  tff(c_145, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_142])).
% 10.59/3.79  tff(c_471, plain, (![B_5, A_98, A_4]: (k5_relat_1(k7_relat_1(B_5, A_98), k6_partfun1(A_4))=k5_relat_1(k6_partfun1(A_98), B_5) | ~v1_relat_1(k6_partfun1(A_4)) | ~v1_relat_1(B_5) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(superposition, [status(thm), theory('equality')], [c_204, c_438])).
% 10.59/3.79  tff(c_4282, plain, (![B_286, A_287, A_288]: (k5_relat_1(k7_relat_1(B_286, A_287), k6_partfun1(A_288))=k5_relat_1(k6_partfun1(A_287), B_286) | ~v5_relat_1(B_286, A_288) | ~v1_relat_1(B_286))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_471])).
% 10.59/3.79  tff(c_4344, plain, (![A_288]: (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k5_relat_1('#skF_4', k6_partfun1(A_288)) | ~v5_relat_1('#skF_4', A_288) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_4282])).
% 10.59/3.79  tff(c_4393, plain, (![A_295]: (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k5_relat_1('#skF_4', k6_partfun1(A_295)) | ~v5_relat_1('#skF_4', A_295))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_4344])).
% 10.59/3.79  tff(c_4418, plain, (![A_295]: (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v5_relat_1('#skF_4', A_295) | ~v1_relat_1('#skF_4') | ~v5_relat_1('#skF_4', A_295))), inference(superposition, [status(thm), theory('equality')], [c_4393, c_204])).
% 10.59/3.79  tff(c_4447, plain, (![A_295]: (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v5_relat_1('#skF_4', A_295))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_4418])).
% 10.59/3.79  tff(c_4455, plain, (![A_295]: (~v5_relat_1('#skF_4', A_295))), inference(splitLeft, [status(thm)], [c_4447])).
% 10.59/3.79  tff(c_121, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_110])).
% 10.59/3.79  tff(c_4457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4455, c_121])).
% 10.59/3.79  tff(c_4458, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_4447])).
% 10.59/3.79  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.59/3.79  tff(c_1551, plain, (![C_155, F_157, D_156, A_153, E_158, B_154]: (k1_partfun1(A_153, B_154, C_155, D_156, E_158, F_157)=k5_relat_1(E_158, F_157) | ~m1_subset_1(F_157, k1_zfmisc_1(k2_zfmisc_1(C_155, D_156))) | ~v1_funct_1(F_157) | ~m1_subset_1(E_158, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))) | ~v1_funct_1(E_158))), inference(cnfTransformation, [status(thm)], [f_118])).
% 10.59/3.79  tff(c_1557, plain, (![A_153, B_154, E_158]: (k1_partfun1(A_153, B_154, '#skF_2', '#skF_1', E_158, '#skF_4')=k5_relat_1(E_158, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_158, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))) | ~v1_funct_1(E_158))), inference(resolution, [status(thm)], [c_60, c_1551])).
% 10.59/3.79  tff(c_1603, plain, (![A_160, B_161, E_162]: (k1_partfun1(A_160, B_161, '#skF_2', '#skF_1', E_162, '#skF_4')=k5_relat_1(E_162, '#skF_4') | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))) | ~v1_funct_1(E_162))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1557])).
% 10.59/3.79  tff(c_1615, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1603])).
% 10.59/3.79  tff(c_1623, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1615])).
% 10.59/3.79  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.59/3.79  tff(c_501, plain, (![D_101, C_102, A_103, B_104]: (D_101=C_102 | ~r2_relset_1(A_103, B_104, C_102, D_101) | ~m1_subset_1(D_101, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.59/3.79  tff(c_509, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_501])).
% 10.59/3.79  tff(c_524, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_509])).
% 10.59/3.79  tff(c_708, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_524])).
% 10.59/3.79  tff(c_1630, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1623, c_708])).
% 10.59/3.79  tff(c_1641, plain, (![A_163, C_165, F_166, E_164, D_167, B_168]: (m1_subset_1(k1_partfun1(A_163, B_168, C_165, D_167, E_164, F_166), k1_zfmisc_1(k2_zfmisc_1(A_163, D_167))) | ~m1_subset_1(F_166, k1_zfmisc_1(k2_zfmisc_1(C_165, D_167))) | ~v1_funct_1(F_166) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(A_163, B_168))) | ~v1_funct_1(E_164))), inference(cnfTransformation, [status(thm)], [f_108])).
% 10.59/3.79  tff(c_1677, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1623, c_1641])).
% 10.59/3.79  tff(c_1696, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_1677])).
% 10.59/3.79  tff(c_1699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1630, c_1696])).
% 10.59/3.79  tff(c_1700, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_524])).
% 10.59/3.79  tff(c_4376, plain, (![F_293, A_289, B_290, C_291, E_294, D_292]: (k1_partfun1(A_289, B_290, C_291, D_292, E_294, F_293)=k5_relat_1(E_294, F_293) | ~m1_subset_1(F_293, k1_zfmisc_1(k2_zfmisc_1(C_291, D_292))) | ~v1_funct_1(F_293) | ~m1_subset_1(E_294, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))) | ~v1_funct_1(E_294))), inference(cnfTransformation, [status(thm)], [f_118])).
% 10.59/3.79  tff(c_4382, plain, (![A_289, B_290, E_294]: (k1_partfun1(A_289, B_290, '#skF_2', '#skF_1', E_294, '#skF_4')=k5_relat_1(E_294, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_294, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))) | ~v1_funct_1(E_294))), inference(resolution, [status(thm)], [c_60, c_4376])).
% 10.59/3.79  tff(c_4459, plain, (![A_296, B_297, E_298]: (k1_partfun1(A_296, B_297, '#skF_2', '#skF_1', E_298, '#skF_4')=k5_relat_1(E_298, '#skF_4') | ~m1_subset_1(E_298, k1_zfmisc_1(k2_zfmisc_1(A_296, B_297))) | ~v1_funct_1(E_298))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_4382])).
% 10.59/3.79  tff(c_4471, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_4459])).
% 10.59/3.79  tff(c_4479, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1700, c_4471])).
% 10.59/3.79  tff(c_18, plain, (![A_21]: (k5_relat_1(k2_funct_1(A_21), A_21)=k6_relat_1(k2_relat_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.59/3.79  tff(c_73, plain, (![A_21]: (k5_relat_1(k2_funct_1(A_21), A_21)=k6_partfun1(k2_relat_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_18])).
% 10.59/3.79  tff(c_6413, plain, (![A_346, C_347]: (k5_relat_1(k6_partfun1(k2_relat_1(A_346)), C_347)=k5_relat_1(k2_funct_1(A_346), k5_relat_1(A_346, C_347)) | ~v1_relat_1(C_347) | ~v1_relat_1(A_346) | ~v1_relat_1(k2_funct_1(A_346)) | ~v2_funct_1(A_346) | ~v1_funct_1(A_346) | ~v1_relat_1(A_346))), inference(superposition, [status(thm), theory('equality')], [c_73, c_326])).
% 10.59/3.79  tff(c_6570, plain, (![C_347]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_347))=k5_relat_1(k6_partfun1('#skF_2'), C_347) | ~v1_relat_1(C_347) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_219, c_6413])).
% 10.59/3.79  tff(c_11041, plain, (![C_443]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_443))=k5_relat_1(k6_partfun1('#skF_2'), C_443) | ~v1_relat_1(C_443))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_70, c_54, c_3612, c_109, c_6570])).
% 10.59/3.79  tff(c_11119, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4479, c_11041])).
% 10.59/3.79  tff(c_11175, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_4458, c_11119])).
% 10.59/3.79  tff(c_11262, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11175, c_204])).
% 10.59/3.79  tff(c_11279, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3612, c_5752, c_11262])).
% 10.59/3.79  tff(c_11281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_11279])).
% 10.59/3.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.59/3.79  
% 10.59/3.79  Inference rules
% 10.59/3.79  ----------------------
% 10.59/3.79  #Ref     : 0
% 10.59/3.79  #Sup     : 2400
% 10.59/3.79  #Fact    : 0
% 10.59/3.79  #Define  : 0
% 10.59/3.79  #Split   : 13
% 10.59/3.79  #Chain   : 0
% 10.59/3.79  #Close   : 0
% 10.59/3.79  
% 10.59/3.79  Ordering : KBO
% 10.59/3.79  
% 10.59/3.79  Simplification rules
% 10.59/3.79  ----------------------
% 10.59/3.79  #Subsume      : 302
% 10.59/3.79  #Demod        : 2988
% 10.59/3.79  #Tautology    : 727
% 10.59/3.79  #SimpNegUnit  : 9
% 10.59/3.79  #BackRed      : 46
% 10.59/3.79  
% 10.59/3.79  #Partial instantiations: 0
% 10.59/3.79  #Strategies tried      : 1
% 10.59/3.79  
% 10.59/3.79  Timing (in seconds)
% 10.59/3.79  ----------------------
% 10.59/3.79  Preprocessing        : 0.37
% 10.59/3.79  Parsing              : 0.21
% 10.59/3.79  CNF conversion       : 0.02
% 10.59/3.79  Main loop            : 2.59
% 10.59/3.79  Inferencing          : 0.75
% 10.59/3.79  Reduction            : 1.18
% 10.59/3.79  Demodulation         : 0.95
% 10.59/3.79  BG Simplification    : 0.08
% 10.59/3.79  Subsumption          : 0.42
% 10.59/3.79  Abstraction          : 0.12
% 10.59/3.79  MUC search           : 0.00
% 10.59/3.79  Cooper               : 0.00
% 10.59/3.79  Total                : 3.02
% 10.59/3.79  Index Insertion      : 0.00
% 10.59/3.79  Index Deletion       : 0.00
% 10.59/3.79  Index Matching       : 0.00
% 10.59/3.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
