%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:00 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 204 expanded)
%              Number of leaves         :   27 (  86 expanded)
%              Depth                    :   12
%              Number of atoms          :  165 ( 617 expanded)
%              Number of equality atoms :   32 ( 100 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r1_partfun1(B,C)
            <=> ! [D] :
                  ( r2_hidden(D,k1_relset_1(A,A,B))
                 => k1_funct_1(B,D) = k1_funct_1(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_2)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
           => ( r1_partfun1(A,B)
            <=> ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).

tff(c_30,plain,
    ( k1_funct_1('#skF_3','#skF_5') != k1_funct_1('#skF_4','#skF_5')
    | ~ r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_55,plain,(
    ~ r1_partfun1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_56,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_56])).

tff(c_28,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_69,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_56])).

tff(c_24,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_81,plain,(
    ! [A_42,B_43,C_44] :
      ( k1_relset_1(A_42,B_43,C_44) = k1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_93,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_81])).

tff(c_117,plain,(
    ! [A_49,B_50,C_51] :
      ( m1_subset_1(k1_relset_1(A_49,B_50,C_51),k1_zfmisc_1(A_49))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_134,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_117])).

tff(c_141,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_134])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_149,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_141,c_2])).

tff(c_22,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_94,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_81])).

tff(c_150,plain,(
    ! [A_52,B_53] :
      ( k1_relset_1(A_52,A_52,B_53) = A_52
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k2_zfmisc_1(A_52,A_52)))
      | ~ v1_funct_2(B_53,A_52,A_52)
      | ~ v1_funct_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_164,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_150])).

tff(c_172,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_94,c_164])).

tff(c_252,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_1'(A_68,B_69),k1_relat_1(A_68))
      | r1_partfun1(A_68,B_69)
      | ~ r1_tarski(k1_relat_1(A_68),k1_relat_1(B_69))
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,(
    ! [D_31] :
      ( r1_partfun1('#skF_3','#skF_4')
      | k1_funct_1('#skF_3',D_31) = k1_funct_1('#skF_4',D_31)
      | ~ r2_hidden(D_31,k1_relset_1('#skF_2','#skF_2','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_103,plain,(
    ! [D_31] :
      ( r1_partfun1('#skF_3','#skF_4')
      | k1_funct_1('#skF_3',D_31) = k1_funct_1('#skF_4',D_31)
      | ~ r2_hidden(D_31,k1_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_40])).

tff(c_104,plain,(
    ! [D_31] :
      ( k1_funct_1('#skF_3',D_31) = k1_funct_1('#skF_4',D_31)
      | ~ r2_hidden(D_31,k1_relat_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_103])).

tff(c_256,plain,(
    ! [B_69] :
      ( k1_funct_1('#skF_3','#skF_1'('#skF_3',B_69)) = k1_funct_1('#skF_4','#skF_1'('#skF_3',B_69))
      | r1_partfun1('#skF_3',B_69)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_69))
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_252,c_104])).

tff(c_305,plain,(
    ! [B_77] :
      ( k1_funct_1('#skF_3','#skF_1'('#skF_3',B_77)) = k1_funct_1('#skF_4','#skF_1'('#skF_3',B_77))
      | r1_partfun1('#skF_3',B_77)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_77))
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_28,c_256])).

tff(c_308,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | r1_partfun1('#skF_3','#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_305])).

tff(c_310,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | r1_partfun1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_24,c_149,c_308])).

tff(c_311,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_310])).

tff(c_319,plain,(
    ! [B_78,A_79] :
      ( k1_funct_1(B_78,'#skF_1'(A_79,B_78)) != k1_funct_1(A_79,'#skF_1'(A_79,B_78))
      | r1_partfun1(A_79,B_78)
      | ~ r1_tarski(k1_relat_1(A_79),k1_relat_1(B_78))
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78)
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_321,plain,
    ( r1_partfun1('#skF_3','#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_319])).

tff(c_324,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_28,c_69,c_24,c_149,c_172,c_321])).

tff(c_326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_324])).

tff(c_327,plain,(
    k1_funct_1('#skF_3','#skF_5') != k1_funct_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_329,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_342,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_329])).

tff(c_356,plain,(
    ! [A_86,B_87,C_88] :
      ( k1_relset_1(A_86,B_87,C_88) = k1_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_368,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_356])).

tff(c_375,plain,(
    ! [A_89,B_90,C_91] :
      ( m1_subset_1(k1_relset_1(A_89,B_90,C_91),k1_zfmisc_1(A_89))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_389,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_375])).

tff(c_394,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_389])).

tff(c_398,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_394,c_2])).

tff(c_328,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_369,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_356])).

tff(c_441,plain,(
    ! [A_98,B_99] :
      ( k1_relset_1(A_98,A_98,B_99) = A_98
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k2_zfmisc_1(A_98,A_98)))
      | ~ v1_funct_2(B_99,A_98,A_98)
      | ~ v1_funct_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_455,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_441])).

tff(c_463,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_369,c_455])).

tff(c_341,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_329])).

tff(c_32,plain,
    ( r2_hidden('#skF_5',k1_relset_1('#skF_2','#skF_2','#skF_3'))
    | ~ r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_344,plain,(
    r2_hidden('#skF_5',k1_relset_1('#skF_2','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_32])).

tff(c_370,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_344])).

tff(c_608,plain,(
    ! [B_141,C_142,A_143] :
      ( k1_funct_1(B_141,C_142) = k1_funct_1(A_143,C_142)
      | ~ r2_hidden(C_142,k1_relat_1(A_143))
      | ~ r1_partfun1(A_143,B_141)
      | ~ r1_tarski(k1_relat_1(A_143),k1_relat_1(B_141))
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141)
      | ~ v1_funct_1(A_143)
      | ~ v1_relat_1(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_614,plain,(
    ! [B_141] :
      ( k1_funct_1(B_141,'#skF_5') = k1_funct_1('#skF_3','#skF_5')
      | ~ r1_partfun1('#skF_3',B_141)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_141))
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_370,c_608])).

tff(c_621,plain,(
    ! [B_144] :
      ( k1_funct_1(B_144,'#skF_5') = k1_funct_1('#skF_3','#skF_5')
      | ~ r1_partfun1('#skF_3',B_144)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_144))
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_28,c_614])).

tff(c_624,plain,
    ( k1_funct_1('#skF_3','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ r1_partfun1('#skF_3','#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_621])).

tff(c_626,plain,(
    k1_funct_1('#skF_3','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_24,c_398,c_328,c_624])).

tff(c_628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_327,c_626])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:07:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.39  
% 2.73/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.39  %$ v1_funct_2 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.73/1.39  
% 2.73/1.39  %Foreground sorts:
% 2.73/1.39  
% 2.73/1.39  
% 2.73/1.39  %Background operators:
% 2.73/1.39  
% 2.73/1.39  
% 2.73/1.39  %Foreground operators:
% 2.73/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.73/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.73/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.73/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.73/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.39  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.73/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.39  
% 2.73/1.41  tff(f_86, negated_conjecture, ~(![A, B]: ((v1_funct_1(B) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_partfun1(B, C) <=> (![D]: (r2_hidden(D, k1_relset_1(A, A, B)) => (k1_funct_1(B, D) = k1_funct_1(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_2)).
% 2.73/1.41  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.73/1.41  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.73/1.41  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.73/1.41  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.73/1.41  tff(f_67, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 2.73/1.41  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) => (r1_partfun1(A, B) <=> (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_partfun1)).
% 2.73/1.41  tff(c_30, plain, (k1_funct_1('#skF_3', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5') | ~r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.73/1.41  tff(c_55, plain, (~r1_partfun1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_30])).
% 2.73/1.41  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.73/1.41  tff(c_56, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.73/1.41  tff(c_68, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_56])).
% 2.73/1.41  tff(c_28, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.73/1.41  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.73/1.41  tff(c_69, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_56])).
% 2.73/1.41  tff(c_24, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.73/1.41  tff(c_81, plain, (![A_42, B_43, C_44]: (k1_relset_1(A_42, B_43, C_44)=k1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.73/1.41  tff(c_93, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_81])).
% 2.73/1.41  tff(c_117, plain, (![A_49, B_50, C_51]: (m1_subset_1(k1_relset_1(A_49, B_50, C_51), k1_zfmisc_1(A_49)) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.73/1.41  tff(c_134, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_93, c_117])).
% 2.73/1.41  tff(c_141, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_134])).
% 2.73/1.41  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.73/1.41  tff(c_149, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_141, c_2])).
% 2.73/1.41  tff(c_22, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.73/1.41  tff(c_94, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_81])).
% 2.73/1.41  tff(c_150, plain, (![A_52, B_53]: (k1_relset_1(A_52, A_52, B_53)=A_52 | ~m1_subset_1(B_53, k1_zfmisc_1(k2_zfmisc_1(A_52, A_52))) | ~v1_funct_2(B_53, A_52, A_52) | ~v1_funct_1(B_53))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.73/1.41  tff(c_164, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_150])).
% 2.73/1.41  tff(c_172, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_94, c_164])).
% 2.73/1.41  tff(c_252, plain, (![A_68, B_69]: (r2_hidden('#skF_1'(A_68, B_69), k1_relat_1(A_68)) | r1_partfun1(A_68, B_69) | ~r1_tarski(k1_relat_1(A_68), k1_relat_1(B_69)) | ~v1_funct_1(B_69) | ~v1_relat_1(B_69) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.73/1.41  tff(c_40, plain, (![D_31]: (r1_partfun1('#skF_3', '#skF_4') | k1_funct_1('#skF_3', D_31)=k1_funct_1('#skF_4', D_31) | ~r2_hidden(D_31, k1_relset_1('#skF_2', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.73/1.41  tff(c_103, plain, (![D_31]: (r1_partfun1('#skF_3', '#skF_4') | k1_funct_1('#skF_3', D_31)=k1_funct_1('#skF_4', D_31) | ~r2_hidden(D_31, k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_40])).
% 2.73/1.41  tff(c_104, plain, (![D_31]: (k1_funct_1('#skF_3', D_31)=k1_funct_1('#skF_4', D_31) | ~r2_hidden(D_31, k1_relat_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_55, c_103])).
% 2.73/1.41  tff(c_256, plain, (![B_69]: (k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_69))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', B_69)) | r1_partfun1('#skF_3', B_69) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_69)) | ~v1_funct_1(B_69) | ~v1_relat_1(B_69) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_252, c_104])).
% 2.73/1.41  tff(c_305, plain, (![B_77]: (k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_77))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', B_77)) | r1_partfun1('#skF_3', B_77) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_77)) | ~v1_funct_1(B_77) | ~v1_relat_1(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_28, c_256])).
% 2.73/1.41  tff(c_308, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | r1_partfun1('#skF_3', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_172, c_305])).
% 2.73/1.41  tff(c_310, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | r1_partfun1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_24, c_149, c_308])).
% 2.73/1.41  tff(c_311, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_55, c_310])).
% 2.73/1.41  tff(c_319, plain, (![B_78, A_79]: (k1_funct_1(B_78, '#skF_1'(A_79, B_78))!=k1_funct_1(A_79, '#skF_1'(A_79, B_78)) | r1_partfun1(A_79, B_78) | ~r1_tarski(k1_relat_1(A_79), k1_relat_1(B_78)) | ~v1_funct_1(B_78) | ~v1_relat_1(B_78) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.73/1.41  tff(c_321, plain, (r1_partfun1('#skF_3', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_311, c_319])).
% 2.73/1.41  tff(c_324, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_28, c_69, c_24, c_149, c_172, c_321])).
% 2.73/1.41  tff(c_326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_324])).
% 2.73/1.41  tff(c_327, plain, (k1_funct_1('#skF_3', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_30])).
% 2.73/1.41  tff(c_329, plain, (![C_80, A_81, B_82]: (v1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.73/1.41  tff(c_342, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_329])).
% 2.73/1.41  tff(c_356, plain, (![A_86, B_87, C_88]: (k1_relset_1(A_86, B_87, C_88)=k1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.73/1.41  tff(c_368, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_356])).
% 2.73/1.41  tff(c_375, plain, (![A_89, B_90, C_91]: (m1_subset_1(k1_relset_1(A_89, B_90, C_91), k1_zfmisc_1(A_89)) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.73/1.41  tff(c_389, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_368, c_375])).
% 2.73/1.41  tff(c_394, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_389])).
% 2.73/1.41  tff(c_398, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_394, c_2])).
% 2.73/1.41  tff(c_328, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_30])).
% 2.73/1.41  tff(c_369, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_356])).
% 2.73/1.41  tff(c_441, plain, (![A_98, B_99]: (k1_relset_1(A_98, A_98, B_99)=A_98 | ~m1_subset_1(B_99, k1_zfmisc_1(k2_zfmisc_1(A_98, A_98))) | ~v1_funct_2(B_99, A_98, A_98) | ~v1_funct_1(B_99))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.73/1.41  tff(c_455, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_441])).
% 2.73/1.41  tff(c_463, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_369, c_455])).
% 2.73/1.41  tff(c_341, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_329])).
% 2.73/1.41  tff(c_32, plain, (r2_hidden('#skF_5', k1_relset_1('#skF_2', '#skF_2', '#skF_3')) | ~r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.73/1.41  tff(c_344, plain, (r2_hidden('#skF_5', k1_relset_1('#skF_2', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_328, c_32])).
% 2.73/1.41  tff(c_370, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_344])).
% 2.73/1.41  tff(c_608, plain, (![B_141, C_142, A_143]: (k1_funct_1(B_141, C_142)=k1_funct_1(A_143, C_142) | ~r2_hidden(C_142, k1_relat_1(A_143)) | ~r1_partfun1(A_143, B_141) | ~r1_tarski(k1_relat_1(A_143), k1_relat_1(B_141)) | ~v1_funct_1(B_141) | ~v1_relat_1(B_141) | ~v1_funct_1(A_143) | ~v1_relat_1(A_143))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.73/1.41  tff(c_614, plain, (![B_141]: (k1_funct_1(B_141, '#skF_5')=k1_funct_1('#skF_3', '#skF_5') | ~r1_partfun1('#skF_3', B_141) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_141)) | ~v1_funct_1(B_141) | ~v1_relat_1(B_141) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_370, c_608])).
% 2.73/1.41  tff(c_621, plain, (![B_144]: (k1_funct_1(B_144, '#skF_5')=k1_funct_1('#skF_3', '#skF_5') | ~r1_partfun1('#skF_3', B_144) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_144)) | ~v1_funct_1(B_144) | ~v1_relat_1(B_144))), inference(demodulation, [status(thm), theory('equality')], [c_341, c_28, c_614])).
% 2.73/1.41  tff(c_624, plain, (k1_funct_1('#skF_3', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~r1_partfun1('#skF_3', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_463, c_621])).
% 2.73/1.41  tff(c_626, plain, (k1_funct_1('#skF_3', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_342, c_24, c_398, c_328, c_624])).
% 2.73/1.41  tff(c_628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_327, c_626])).
% 2.73/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.41  
% 2.73/1.41  Inference rules
% 2.73/1.41  ----------------------
% 2.73/1.41  #Ref     : 2
% 2.73/1.41  #Sup     : 118
% 2.73/1.41  #Fact    : 0
% 2.73/1.41  #Define  : 0
% 2.73/1.41  #Split   : 3
% 2.73/1.41  #Chain   : 0
% 2.73/1.41  #Close   : 0
% 2.73/1.41  
% 2.73/1.41  Ordering : KBO
% 2.73/1.41  
% 2.73/1.41  Simplification rules
% 2.73/1.41  ----------------------
% 2.73/1.41  #Subsume      : 9
% 2.73/1.41  #Demod        : 111
% 2.73/1.41  #Tautology    : 45
% 2.73/1.41  #SimpNegUnit  : 4
% 2.73/1.41  #BackRed      : 7
% 2.73/1.41  
% 2.73/1.41  #Partial instantiations: 0
% 2.73/1.41  #Strategies tried      : 1
% 2.73/1.41  
% 2.73/1.41  Timing (in seconds)
% 2.73/1.41  ----------------------
% 2.73/1.41  Preprocessing        : 0.31
% 2.73/1.41  Parsing              : 0.17
% 2.73/1.41  CNF conversion       : 0.02
% 2.73/1.41  Main loop            : 0.33
% 2.73/1.41  Inferencing          : 0.14
% 2.73/1.41  Reduction            : 0.09
% 2.73/1.41  Demodulation         : 0.07
% 2.73/1.41  BG Simplification    : 0.02
% 2.73/1.41  Subsumption          : 0.05
% 2.73/1.41  Abstraction          : 0.02
% 2.73/1.41  MUC search           : 0.00
% 2.73/1.41  Cooper               : 0.00
% 2.73/1.41  Total                : 0.68
% 2.73/1.41  Index Insertion      : 0.00
% 2.73/1.41  Index Deletion       : 0.00
% 2.73/1.41  Index Matching       : 0.00
% 2.73/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
