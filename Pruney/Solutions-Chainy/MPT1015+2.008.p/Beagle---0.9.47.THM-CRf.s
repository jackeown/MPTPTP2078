%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:38 EST 2020

% Result     : Theorem 4.20s
% Output     : CNFRefutation 4.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 173 expanded)
%              Number of leaves         :   35 (  80 expanded)
%              Depth                    :    9
%              Number of atoms          :  158 ( 577 expanded)
%              Number of equality atoms :   39 (  62 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,C,B),B)
                & v2_funct_1(B) )
             => r2_relset_1(A,A,C,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_98,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_108,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_110,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( ( k1_relat_1(B) = A
              & k1_relat_1(C) = A
              & r1_tarski(k2_relat_1(C),A)
              & v2_funct_1(B)
              & k5_relat_1(C,B) = B )
           => C = k6_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_164,plain,(
    ! [A_66,B_67,D_68] :
      ( r2_relset_1(A_66,B_67,D_68,D_68)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_174,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_164])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_81,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_93,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_81])).

tff(c_54,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_94,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_81])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_52,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_204,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_216,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_204])).

tff(c_497,plain,(
    ! [A_108,B_109] :
      ( k1_relset_1(A_108,A_108,B_109) = A_108
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_zfmisc_1(A_108,A_108)))
      | ~ v1_funct_2(B_109,A_108,A_108)
      | ~ v1_funct_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_508,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_497])).

tff(c_516,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_216,c_508])).

tff(c_46,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_217,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_204])).

tff(c_511,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_497])).

tff(c_519,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_217,c_511])).

tff(c_293,plain,(
    ! [A_89,B_90,C_91] :
      ( k2_relset_1(A_89,B_90,C_91) = k2_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_306,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_293])).

tff(c_412,plain,(
    ! [A_103,B_104,C_105] :
      ( m1_subset_1(k2_relset_1(A_103,B_104,C_105),k1_zfmisc_1(B_104))
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_436,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_412])).

tff(c_446,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_436])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_452,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_446,c_10])).

tff(c_40,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_28,plain,(
    ! [C_30,E_32,D_31,B_29,F_33,A_28] :
      ( m1_subset_1(k1_partfun1(A_28,B_29,C_30,D_31,E_32,F_33),k1_zfmisc_1(k2_zfmisc_1(A_28,D_31)))
      | ~ m1_subset_1(F_33,k1_zfmisc_1(k2_zfmisc_1(C_30,D_31)))
      | ~ v1_funct_1(F_33)
      | ~ m1_subset_1(E_32,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_1(E_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_42,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_540,plain,(
    ! [D_110,C_111,A_112,B_113] :
      ( D_110 = C_111
      | ~ r2_relset_1(A_112,B_113,C_111,D_110)
      | ~ m1_subset_1(D_110,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_552,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_42,c_540])).

tff(c_569,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_552])).

tff(c_587,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_569])).

tff(c_1402,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_587])).

tff(c_1409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_54,c_50,c_1402])).

tff(c_1410,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_569])).

tff(c_1789,plain,(
    ! [D_227,C_231,F_228,E_229,A_226,B_230] :
      ( k1_partfun1(A_226,B_230,C_231,D_227,E_229,F_228) = k5_relat_1(E_229,F_228)
      | ~ m1_subset_1(F_228,k1_zfmisc_1(k2_zfmisc_1(C_231,D_227)))
      | ~ v1_funct_1(F_228)
      | ~ m1_subset_1(E_229,k1_zfmisc_1(k2_zfmisc_1(A_226,B_230)))
      | ~ v1_funct_1(E_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1797,plain,(
    ! [A_226,B_230,E_229] :
      ( k1_partfun1(A_226,B_230,'#skF_1','#skF_1',E_229,'#skF_2') = k5_relat_1(E_229,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_229,k1_zfmisc_1(k2_zfmisc_1(A_226,B_230)))
      | ~ v1_funct_1(E_229) ) ),
    inference(resolution,[status(thm)],[c_50,c_1789])).

tff(c_2145,plain,(
    ! [A_270,B_271,E_272] :
      ( k1_partfun1(A_270,B_271,'#skF_1','#skF_1',E_272,'#skF_2') = k5_relat_1(E_272,'#skF_2')
      | ~ m1_subset_1(E_272,k1_zfmisc_1(k2_zfmisc_1(A_270,B_271)))
      | ~ v1_funct_1(E_272) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1797])).

tff(c_2165,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_2145])).

tff(c_2177,plain,(
    k5_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1410,c_2165])).

tff(c_34,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_14,plain,(
    ! [C_11,B_9] :
      ( k6_relat_1(k1_relat_1(C_11)) = C_11
      | k5_relat_1(C_11,B_9) != B_9
      | ~ v2_funct_1(B_9)
      | ~ r1_tarski(k2_relat_1(C_11),k1_relat_1(C_11))
      | k1_relat_1(C_11) != k1_relat_1(B_9)
      | ~ v1_funct_1(C_11)
      | ~ v1_relat_1(C_11)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_55,plain,(
    ! [C_11,B_9] :
      ( k6_partfun1(k1_relat_1(C_11)) = C_11
      | k5_relat_1(C_11,B_9) != B_9
      | ~ v2_funct_1(B_9)
      | ~ r1_tarski(k2_relat_1(C_11),k1_relat_1(C_11))
      | k1_relat_1(C_11) != k1_relat_1(B_9)
      | ~ v1_funct_1(C_11)
      | ~ v1_relat_1(C_11)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14])).

tff(c_2180,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v2_funct_1('#skF_2')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k1_relat_1('#skF_2') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2177,c_55])).

tff(c_2185,plain,(
    k6_partfun1('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_54,c_94,c_48,c_516,c_519,c_452,c_519,c_40,c_519,c_2180])).

tff(c_38,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2187,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2185,c_38])).

tff(c_2190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_2187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.20/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/1.73  
% 4.20/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/1.73  %$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.20/1.73  
% 4.20/1.73  %Foreground sorts:
% 4.20/1.73  
% 4.20/1.73  
% 4.20/1.73  %Background operators:
% 4.20/1.73  
% 4.20/1.73  
% 4.20/1.73  %Foreground operators:
% 4.20/1.73  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.20/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.20/1.73  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.20/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.20/1.73  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.20/1.73  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.20/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.20/1.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.20/1.73  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.20/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.20/1.73  tff('#skF_2', type, '#skF_2': $i).
% 4.20/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.20/1.73  tff('#skF_1', type, '#skF_1': $i).
% 4.20/1.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.20/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.20/1.73  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.20/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.20/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.20/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.20/1.73  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.20/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.20/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.20/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.20/1.73  
% 4.20/1.75  tff(f_138, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r2_relset_1(A, A, k1_partfun1(A, A, A, A, C, B), B) & v2_funct_1(B)) => r2_relset_1(A, A, C, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_funct_2)).
% 4.20/1.75  tff(f_86, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.20/1.75  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.20/1.75  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.20/1.75  tff(f_118, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 4.20/1.75  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.20/1.75  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.20/1.75  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.20/1.75  tff(f_98, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.20/1.75  tff(f_108, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.20/1.75  tff(f_110, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.20/1.75  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) & r1_tarski(k2_relat_1(C), A)) & v2_funct_1(B)) & (k5_relat_1(C, B) = B)) => (C = k6_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_funct_1)).
% 4.20/1.75  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.20/1.75  tff(c_164, plain, (![A_66, B_67, D_68]: (r2_relset_1(A_66, B_67, D_68, D_68) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.20/1.75  tff(c_174, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_164])).
% 4.20/1.75  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.20/1.75  tff(c_81, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.20/1.75  tff(c_93, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_81])).
% 4.20/1.75  tff(c_54, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.20/1.75  tff(c_94, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_81])).
% 4.20/1.75  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.20/1.75  tff(c_52, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.20/1.75  tff(c_204, plain, (![A_74, B_75, C_76]: (k1_relset_1(A_74, B_75, C_76)=k1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.20/1.75  tff(c_216, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_204])).
% 4.20/1.75  tff(c_497, plain, (![A_108, B_109]: (k1_relset_1(A_108, A_108, B_109)=A_108 | ~m1_subset_1(B_109, k1_zfmisc_1(k2_zfmisc_1(A_108, A_108))) | ~v1_funct_2(B_109, A_108, A_108) | ~v1_funct_1(B_109))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.20/1.75  tff(c_508, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_497])).
% 4.20/1.75  tff(c_516, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_216, c_508])).
% 4.20/1.75  tff(c_46, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.20/1.75  tff(c_217, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_204])).
% 4.20/1.75  tff(c_511, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_497])).
% 4.20/1.75  tff(c_519, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_217, c_511])).
% 4.20/1.75  tff(c_293, plain, (![A_89, B_90, C_91]: (k2_relset_1(A_89, B_90, C_91)=k2_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.20/1.75  tff(c_306, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_293])).
% 4.20/1.75  tff(c_412, plain, (![A_103, B_104, C_105]: (m1_subset_1(k2_relset_1(A_103, B_104, C_105), k1_zfmisc_1(B_104)) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.20/1.75  tff(c_436, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_306, c_412])).
% 4.20/1.75  tff(c_446, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_436])).
% 4.20/1.75  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.20/1.75  tff(c_452, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_446, c_10])).
% 4.20/1.75  tff(c_40, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.20/1.75  tff(c_28, plain, (![C_30, E_32, D_31, B_29, F_33, A_28]: (m1_subset_1(k1_partfun1(A_28, B_29, C_30, D_31, E_32, F_33), k1_zfmisc_1(k2_zfmisc_1(A_28, D_31))) | ~m1_subset_1(F_33, k1_zfmisc_1(k2_zfmisc_1(C_30, D_31))) | ~v1_funct_1(F_33) | ~m1_subset_1(E_32, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_1(E_32))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.20/1.75  tff(c_42, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.20/1.75  tff(c_540, plain, (![D_110, C_111, A_112, B_113]: (D_110=C_111 | ~r2_relset_1(A_112, B_113, C_111, D_110) | ~m1_subset_1(D_110, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.20/1.75  tff(c_552, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_42, c_540])).
% 4.20/1.75  tff(c_569, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_552])).
% 4.20/1.75  tff(c_587, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_569])).
% 4.20/1.75  tff(c_1402, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_587])).
% 4.20/1.75  tff(c_1409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_54, c_50, c_1402])).
% 4.20/1.75  tff(c_1410, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_569])).
% 4.20/1.75  tff(c_1789, plain, (![D_227, C_231, F_228, E_229, A_226, B_230]: (k1_partfun1(A_226, B_230, C_231, D_227, E_229, F_228)=k5_relat_1(E_229, F_228) | ~m1_subset_1(F_228, k1_zfmisc_1(k2_zfmisc_1(C_231, D_227))) | ~v1_funct_1(F_228) | ~m1_subset_1(E_229, k1_zfmisc_1(k2_zfmisc_1(A_226, B_230))) | ~v1_funct_1(E_229))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.20/1.75  tff(c_1797, plain, (![A_226, B_230, E_229]: (k1_partfun1(A_226, B_230, '#skF_1', '#skF_1', E_229, '#skF_2')=k5_relat_1(E_229, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_229, k1_zfmisc_1(k2_zfmisc_1(A_226, B_230))) | ~v1_funct_1(E_229))), inference(resolution, [status(thm)], [c_50, c_1789])).
% 4.20/1.75  tff(c_2145, plain, (![A_270, B_271, E_272]: (k1_partfun1(A_270, B_271, '#skF_1', '#skF_1', E_272, '#skF_2')=k5_relat_1(E_272, '#skF_2') | ~m1_subset_1(E_272, k1_zfmisc_1(k2_zfmisc_1(A_270, B_271))) | ~v1_funct_1(E_272))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1797])).
% 4.20/1.75  tff(c_2165, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_2145])).
% 4.20/1.75  tff(c_2177, plain, (k5_relat_1('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1410, c_2165])).
% 4.20/1.75  tff(c_34, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.20/1.75  tff(c_14, plain, (![C_11, B_9]: (k6_relat_1(k1_relat_1(C_11))=C_11 | k5_relat_1(C_11, B_9)!=B_9 | ~v2_funct_1(B_9) | ~r1_tarski(k2_relat_1(C_11), k1_relat_1(C_11)) | k1_relat_1(C_11)!=k1_relat_1(B_9) | ~v1_funct_1(C_11) | ~v1_relat_1(C_11) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.20/1.75  tff(c_55, plain, (![C_11, B_9]: (k6_partfun1(k1_relat_1(C_11))=C_11 | k5_relat_1(C_11, B_9)!=B_9 | ~v2_funct_1(B_9) | ~r1_tarski(k2_relat_1(C_11), k1_relat_1(C_11)) | k1_relat_1(C_11)!=k1_relat_1(B_9) | ~v1_funct_1(C_11) | ~v1_relat_1(C_11) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_14])).
% 4.20/1.75  tff(c_2180, plain, (k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v2_funct_1('#skF_2') | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k1_relat_1('#skF_2')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2177, c_55])).
% 4.20/1.75  tff(c_2185, plain, (k6_partfun1('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_54, c_94, c_48, c_516, c_519, c_452, c_519, c_40, c_519, c_2180])).
% 4.20/1.75  tff(c_38, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.20/1.75  tff(c_2187, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2185, c_38])).
% 4.20/1.75  tff(c_2190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_174, c_2187])).
% 4.20/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/1.75  
% 4.20/1.75  Inference rules
% 4.20/1.75  ----------------------
% 4.20/1.75  #Ref     : 0
% 4.20/1.75  #Sup     : 478
% 4.20/1.75  #Fact    : 0
% 4.20/1.75  #Define  : 0
% 4.20/1.75  #Split   : 7
% 4.20/1.75  #Chain   : 0
% 4.20/1.75  #Close   : 0
% 4.20/1.75  
% 4.20/1.75  Ordering : KBO
% 4.20/1.75  
% 4.20/1.75  Simplification rules
% 4.20/1.75  ----------------------
% 4.20/1.75  #Subsume      : 48
% 4.20/1.75  #Demod        : 170
% 4.20/1.75  #Tautology    : 86
% 4.20/1.75  #SimpNegUnit  : 0
% 4.20/1.75  #BackRed      : 8
% 4.20/1.75  
% 4.20/1.75  #Partial instantiations: 0
% 4.20/1.75  #Strategies tried      : 1
% 4.20/1.75  
% 4.20/1.75  Timing (in seconds)
% 4.20/1.75  ----------------------
% 4.20/1.75  Preprocessing        : 0.33
% 4.20/1.75  Parsing              : 0.18
% 4.20/1.75  CNF conversion       : 0.02
% 4.20/1.75  Main loop            : 0.65
% 4.20/1.75  Inferencing          : 0.22
% 4.20/1.75  Reduction            : 0.21
% 4.20/1.75  Demodulation         : 0.16
% 4.20/1.75  BG Simplification    : 0.03
% 4.20/1.75  Subsumption          : 0.13
% 4.20/1.75  Abstraction          : 0.03
% 4.20/1.75  MUC search           : 0.00
% 4.20/1.75  Cooper               : 0.00
% 4.20/1.75  Total                : 1.02
% 4.20/1.75  Index Insertion      : 0.00
% 4.20/1.75  Index Deletion       : 0.00
% 4.20/1.75  Index Matching       : 0.00
% 4.20/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
