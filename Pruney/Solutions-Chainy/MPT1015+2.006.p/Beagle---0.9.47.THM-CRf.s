%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:38 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 255 expanded)
%              Number of leaves         :   39 ( 109 expanded)
%              Depth                    :   16
%              Number of atoms          :  177 ( 827 expanded)
%              Number of equality atoms :   39 (  89 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_139,negated_conjecture,(
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

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_111,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_99,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_109,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_118,plain,(
    ! [A_63,B_64,D_65] :
      ( r2_relset_1(A_63,B_64,D_65,D_65)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_124,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_118])).

tff(c_71,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_79,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_71])).

tff(c_95,plain,(
    ! [C_56,B_57,A_58] :
      ( v5_relat_1(C_56,B_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_58,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_103,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_95])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_78,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_71])).

tff(c_56,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_42,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_54,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_125,plain,(
    ! [A_66,B_67,C_68] :
      ( k1_relset_1(A_66,B_67,C_68) = k1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_132,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_125])).

tff(c_208,plain,(
    ! [A_74,B_75] :
      ( k1_relset_1(A_74,A_74,B_75) = A_74
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k2_zfmisc_1(A_74,A_74)))
      | ~ v1_funct_2(B_75,A_74,A_74)
      | ~ v1_funct_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_211,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_208])).

tff(c_217,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_132,c_211])).

tff(c_12,plain,(
    ! [A_12] :
      ( v1_relat_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_36,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_16,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k2_funct_1(A_13)) = k6_relat_1(k1_relat_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_57,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k2_funct_1(A_13)) = k6_partfun1(k1_relat_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_16])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_373,plain,(
    ! [A_109,C_105,B_108,F_104,E_107,D_106] :
      ( m1_subset_1(k1_partfun1(A_109,B_108,C_105,D_106,E_107,F_104),k1_zfmisc_1(k2_zfmisc_1(A_109,D_106)))
      | ~ m1_subset_1(F_104,k1_zfmisc_1(k2_zfmisc_1(C_105,D_106)))
      | ~ v1_funct_1(F_104)
      | ~ m1_subset_1(E_107,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108)))
      | ~ v1_funct_1(E_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_44,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_221,plain,(
    ! [D_76,C_77,A_78,B_79] :
      ( D_76 = C_77
      | ~ r2_relset_1(A_78,B_79,C_77,D_76)
      | ~ m1_subset_1(D_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_227,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_44,c_221])).

tff(c_238,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_227])).

tff(c_257,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_238])).

tff(c_389,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_373,c_257])).

tff(c_422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_56,c_52,c_389])).

tff(c_423,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_513,plain,(
    ! [E_126,F_128,D_129,B_130,C_127,A_125] :
      ( k1_partfun1(A_125,B_130,C_127,D_129,E_126,F_128) = k5_relat_1(E_126,F_128)
      | ~ m1_subset_1(F_128,k1_zfmisc_1(k2_zfmisc_1(C_127,D_129)))
      | ~ v1_funct_1(F_128)
      | ~ m1_subset_1(E_126,k1_zfmisc_1(k2_zfmisc_1(A_125,B_130)))
      | ~ v1_funct_1(E_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_515,plain,(
    ! [A_125,B_130,E_126] :
      ( k1_partfun1(A_125,B_130,'#skF_1','#skF_1',E_126,'#skF_2') = k5_relat_1(E_126,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_126,k1_zfmisc_1(k2_zfmisc_1(A_125,B_130)))
      | ~ v1_funct_1(E_126) ) ),
    inference(resolution,[status(thm)],[c_52,c_513])).

tff(c_524,plain,(
    ! [A_131,B_132,E_133] :
      ( k1_partfun1(A_131,B_132,'#skF_1','#skF_1',E_133,'#skF_2') = k5_relat_1(E_133,'#skF_2')
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_1(E_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_515])).

tff(c_530,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_524])).

tff(c_536,plain,(
    k5_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_423,c_530])).

tff(c_6,plain,(
    ! [A_3,B_7,C_9] :
      ( k5_relat_1(k5_relat_1(A_3,B_7),C_9) = k5_relat_1(A_3,k5_relat_1(B_7,C_9))
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_540,plain,(
    ! [C_9] :
      ( k5_relat_1('#skF_3',k5_relat_1('#skF_2',C_9)) = k5_relat_1('#skF_2',C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_6])).

tff(c_979,plain,(
    ! [C_154] :
      ( k5_relat_1('#skF_3',k5_relat_1('#skF_2',C_154)) = k5_relat_1('#skF_2',C_154)
      | ~ v1_relat_1(C_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_78,c_540])).

tff(c_996,plain,
    ( k5_relat_1('#skF_3',k6_partfun1(k1_relat_1('#skF_2'))) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_979])).

tff(c_1008,plain,
    ( k5_relat_1('#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_3',k6_partfun1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_56,c_42,c_217,c_996])).

tff(c_1247,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1008])).

tff(c_1279,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_1247])).

tff(c_1283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_56,c_1279])).

tff(c_1284,plain,(
    k5_relat_1('#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_3',k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1008])).

tff(c_1295,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_1')) = k6_partfun1(k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1284,c_57])).

tff(c_1306,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_1')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_56,c_42,c_217,c_1295])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_relat_1(A_10)) = B_11
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_104,plain,(
    ! [B_59,A_60] :
      ( k5_relat_1(B_59,k6_partfun1(A_60)) = B_59
      | ~ r1_tarski(k2_relat_1(B_59),A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8])).

tff(c_108,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_partfun1(A_1)) = B_2
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_104])).

tff(c_1352,plain,
    ( k6_partfun1('#skF_1') = '#skF_3'
    | ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1306,c_108])).

tff(c_1361,plain,(
    k6_partfun1('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_103,c_1352])).

tff(c_40,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1366,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1361,c_40])).

tff(c_1369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_1366])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:10:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.02/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.71  
% 4.02/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.71  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.02/1.71  
% 4.02/1.71  %Foreground sorts:
% 4.02/1.71  
% 4.02/1.71  
% 4.02/1.71  %Background operators:
% 4.02/1.71  
% 4.02/1.71  
% 4.02/1.71  %Foreground operators:
% 4.02/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.02/1.71  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.02/1.71  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.02/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.02/1.71  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.02/1.71  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.02/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.02/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.02/1.71  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.02/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.02/1.71  tff('#skF_2', type, '#skF_2': $i).
% 4.02/1.71  tff('#skF_3', type, '#skF_3': $i).
% 4.02/1.71  tff('#skF_1', type, '#skF_1': $i).
% 4.02/1.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.02/1.71  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.02/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.02/1.71  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.02/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.02/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.02/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.02/1.71  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.02/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.02/1.71  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.02/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.02/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.02/1.71  
% 4.02/1.72  tff(f_139, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r2_relset_1(A, A, k1_partfun1(A, A, A, A, C, B), B) & v2_funct_1(B)) => r2_relset_1(A, A, C, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_funct_2)).
% 4.02/1.72  tff(f_87, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.02/1.72  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.02/1.72  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.02/1.72  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.02/1.72  tff(f_119, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 4.02/1.72  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.02/1.72  tff(f_111, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.02/1.72  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 4.02/1.72  tff(f_99, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.02/1.72  tff(f_109, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.02/1.72  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 4.02/1.72  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.02/1.72  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 4.02/1.72  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.02/1.72  tff(c_118, plain, (![A_63, B_64, D_65]: (r2_relset_1(A_63, B_64, D_65, D_65) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.02/1.72  tff(c_124, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_118])).
% 4.02/1.72  tff(c_71, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.02/1.72  tff(c_79, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_71])).
% 4.02/1.72  tff(c_95, plain, (![C_56, B_57, A_58]: (v5_relat_1(C_56, B_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_58, B_57))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.02/1.72  tff(c_103, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_95])).
% 4.02/1.72  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.02/1.72  tff(c_78, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_71])).
% 4.02/1.72  tff(c_56, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.02/1.72  tff(c_42, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.02/1.72  tff(c_54, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.02/1.72  tff(c_125, plain, (![A_66, B_67, C_68]: (k1_relset_1(A_66, B_67, C_68)=k1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.02/1.72  tff(c_132, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_125])).
% 4.02/1.72  tff(c_208, plain, (![A_74, B_75]: (k1_relset_1(A_74, A_74, B_75)=A_74 | ~m1_subset_1(B_75, k1_zfmisc_1(k2_zfmisc_1(A_74, A_74))) | ~v1_funct_2(B_75, A_74, A_74) | ~v1_funct_1(B_75))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.02/1.72  tff(c_211, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_208])).
% 4.02/1.72  tff(c_217, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_132, c_211])).
% 4.02/1.72  tff(c_12, plain, (![A_12]: (v1_relat_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.02/1.72  tff(c_36, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.02/1.72  tff(c_16, plain, (![A_13]: (k5_relat_1(A_13, k2_funct_1(A_13))=k6_relat_1(k1_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.02/1.72  tff(c_57, plain, (![A_13]: (k5_relat_1(A_13, k2_funct_1(A_13))=k6_partfun1(k1_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_16])).
% 4.02/1.72  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.02/1.72  tff(c_373, plain, (![A_109, C_105, B_108, F_104, E_107, D_106]: (m1_subset_1(k1_partfun1(A_109, B_108, C_105, D_106, E_107, F_104), k1_zfmisc_1(k2_zfmisc_1(A_109, D_106))) | ~m1_subset_1(F_104, k1_zfmisc_1(k2_zfmisc_1(C_105, D_106))) | ~v1_funct_1(F_104) | ~m1_subset_1(E_107, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))) | ~v1_funct_1(E_107))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.02/1.72  tff(c_44, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.02/1.72  tff(c_221, plain, (![D_76, C_77, A_78, B_79]: (D_76=C_77 | ~r2_relset_1(A_78, B_79, C_77, D_76) | ~m1_subset_1(D_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.02/1.72  tff(c_227, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_44, c_221])).
% 4.02/1.72  tff(c_238, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_227])).
% 4.02/1.72  tff(c_257, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_238])).
% 4.02/1.72  tff(c_389, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_373, c_257])).
% 4.02/1.72  tff(c_422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_56, c_52, c_389])).
% 4.02/1.72  tff(c_423, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_238])).
% 4.02/1.72  tff(c_513, plain, (![E_126, F_128, D_129, B_130, C_127, A_125]: (k1_partfun1(A_125, B_130, C_127, D_129, E_126, F_128)=k5_relat_1(E_126, F_128) | ~m1_subset_1(F_128, k1_zfmisc_1(k2_zfmisc_1(C_127, D_129))) | ~v1_funct_1(F_128) | ~m1_subset_1(E_126, k1_zfmisc_1(k2_zfmisc_1(A_125, B_130))) | ~v1_funct_1(E_126))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.02/1.72  tff(c_515, plain, (![A_125, B_130, E_126]: (k1_partfun1(A_125, B_130, '#skF_1', '#skF_1', E_126, '#skF_2')=k5_relat_1(E_126, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_126, k1_zfmisc_1(k2_zfmisc_1(A_125, B_130))) | ~v1_funct_1(E_126))), inference(resolution, [status(thm)], [c_52, c_513])).
% 4.02/1.72  tff(c_524, plain, (![A_131, B_132, E_133]: (k1_partfun1(A_131, B_132, '#skF_1', '#skF_1', E_133, '#skF_2')=k5_relat_1(E_133, '#skF_2') | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~v1_funct_1(E_133))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_515])).
% 4.02/1.72  tff(c_530, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_524])).
% 4.02/1.72  tff(c_536, plain, (k5_relat_1('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_423, c_530])).
% 4.02/1.72  tff(c_6, plain, (![A_3, B_7, C_9]: (k5_relat_1(k5_relat_1(A_3, B_7), C_9)=k5_relat_1(A_3, k5_relat_1(B_7, C_9)) | ~v1_relat_1(C_9) | ~v1_relat_1(B_7) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.02/1.72  tff(c_540, plain, (![C_9]: (k5_relat_1('#skF_3', k5_relat_1('#skF_2', C_9))=k5_relat_1('#skF_2', C_9) | ~v1_relat_1(C_9) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_536, c_6])).
% 4.02/1.72  tff(c_979, plain, (![C_154]: (k5_relat_1('#skF_3', k5_relat_1('#skF_2', C_154))=k5_relat_1('#skF_2', C_154) | ~v1_relat_1(C_154))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_78, c_540])).
% 4.02/1.72  tff(c_996, plain, (k5_relat_1('#skF_3', k6_partfun1(k1_relat_1('#skF_2')))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_57, c_979])).
% 4.02/1.72  tff(c_1008, plain, (k5_relat_1('#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_3', k6_partfun1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_56, c_42, c_217, c_996])).
% 4.02/1.72  tff(c_1247, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1008])).
% 4.02/1.72  tff(c_1279, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_1247])).
% 4.02/1.72  tff(c_1283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_56, c_1279])).
% 4.02/1.72  tff(c_1284, plain, (k5_relat_1('#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_3', k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_1008])).
% 4.02/1.72  tff(c_1295, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_1'))=k6_partfun1(k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1284, c_57])).
% 4.02/1.72  tff(c_1306, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_1'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_56, c_42, c_217, c_1295])).
% 4.02/1.73  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.02/1.73  tff(c_8, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_relat_1(A_10))=B_11 | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.02/1.73  tff(c_104, plain, (![B_59, A_60]: (k5_relat_1(B_59, k6_partfun1(A_60))=B_59 | ~r1_tarski(k2_relat_1(B_59), A_60) | ~v1_relat_1(B_59))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8])).
% 4.02/1.73  tff(c_108, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_partfun1(A_1))=B_2 | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_104])).
% 4.02/1.73  tff(c_1352, plain, (k6_partfun1('#skF_1')='#skF_3' | ~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1306, c_108])).
% 4.02/1.73  tff(c_1361, plain, (k6_partfun1('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_103, c_1352])).
% 4.02/1.73  tff(c_40, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.02/1.73  tff(c_1366, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1361, c_40])).
% 4.02/1.73  tff(c_1369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_1366])).
% 4.02/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.73  
% 4.02/1.73  Inference rules
% 4.02/1.73  ----------------------
% 4.02/1.73  #Ref     : 0
% 4.02/1.73  #Sup     : 301
% 4.02/1.73  #Fact    : 0
% 4.02/1.73  #Define  : 0
% 4.02/1.73  #Split   : 2
% 4.02/1.73  #Chain   : 0
% 4.02/1.73  #Close   : 0
% 4.02/1.73  
% 4.02/1.73  Ordering : KBO
% 4.02/1.73  
% 4.02/1.73  Simplification rules
% 4.02/1.73  ----------------------
% 4.02/1.73  #Subsume      : 0
% 4.02/1.73  #Demod        : 196
% 4.02/1.73  #Tautology    : 78
% 4.02/1.73  #SimpNegUnit  : 0
% 4.02/1.73  #BackRed      : 11
% 4.02/1.73  
% 4.02/1.73  #Partial instantiations: 0
% 4.02/1.73  #Strategies tried      : 1
% 4.02/1.73  
% 4.02/1.73  Timing (in seconds)
% 4.02/1.73  ----------------------
% 4.02/1.73  Preprocessing        : 0.37
% 4.02/1.73  Parsing              : 0.21
% 4.02/1.73  CNF conversion       : 0.02
% 4.02/1.73  Main loop            : 0.52
% 4.02/1.73  Inferencing          : 0.20
% 4.02/1.73  Reduction            : 0.16
% 4.02/1.73  Demodulation         : 0.12
% 4.02/1.73  BG Simplification    : 0.03
% 4.02/1.73  Subsumption          : 0.09
% 4.02/1.73  Abstraction          : 0.03
% 4.02/1.73  MUC search           : 0.00
% 4.02/1.73  Cooper               : 0.00
% 4.02/1.73  Total                : 0.93
% 4.02/1.73  Index Insertion      : 0.00
% 4.02/1.73  Index Deletion       : 0.00
% 4.02/1.73  Index Matching       : 0.00
% 4.02/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
