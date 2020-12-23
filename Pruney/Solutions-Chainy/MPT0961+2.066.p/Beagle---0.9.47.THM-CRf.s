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
% DateTime   : Thu Dec  3 10:10:50 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 855 expanded)
%              Number of leaves         :   26 ( 288 expanded)
%              Depth                    :   12
%              Number of atoms          :  182 (2107 expanded)
%              Number of equality atoms :   79 ( 721 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_37,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_42,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_977,plain,(
    ! [A_136] :
      ( r1_tarski(A_136,k2_zfmisc_1(k1_relat_1(A_136),k2_relat_1(A_136)))
      | ~ v1_relat_1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_6] :
      ( r1_tarski(A_6,k2_zfmisc_1(k1_relat_1(A_6),k2_relat_1(A_6)))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_351,plain,(
    ! [A_69,B_70,C_71] :
      ( k1_relset_1(A_69,B_70,C_71) = k1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_431,plain,(
    ! [A_87,B_88,A_89] :
      ( k1_relset_1(A_87,B_88,A_89) = k1_relat_1(A_89)
      | ~ r1_tarski(A_89,k2_zfmisc_1(A_87,B_88)) ) ),
    inference(resolution,[status(thm)],[c_10,c_351])).

tff(c_441,plain,(
    ! [A_6] :
      ( k1_relset_1(k1_relat_1(A_6),k2_relat_1(A_6),A_6) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_431])).

tff(c_363,plain,(
    ! [B_72,C_73,A_74] :
      ( k1_xboole_0 = B_72
      | v1_funct_2(C_73,A_74,B_72)
      | k1_relset_1(A_74,B_72,C_73) != A_74
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_779,plain,(
    ! [B_122,A_123,A_124] :
      ( k1_xboole_0 = B_122
      | v1_funct_2(A_123,A_124,B_122)
      | k1_relset_1(A_124,B_122,A_123) != A_124
      | ~ r1_tarski(A_123,k2_zfmisc_1(A_124,B_122)) ) ),
    inference(resolution,[status(thm)],[c_10,c_363])).

tff(c_822,plain,(
    ! [A_130] :
      ( k2_relat_1(A_130) = k1_xboole_0
      | v1_funct_2(A_130,k1_relat_1(A_130),k2_relat_1(A_130))
      | k1_relset_1(k1_relat_1(A_130),k2_relat_1(A_130),A_130) != k1_relat_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(resolution,[status(thm)],[c_14,c_779])).

tff(c_36,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_40,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34])).

tff(c_95,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_825,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_822,c_95])).

tff(c_831,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_825])).

tff(c_834,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_831])).

tff(c_837,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_834])).

tff(c_841,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_837])).

tff(c_842,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_831])).

tff(c_854,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_842,c_14])).

tff(c_862,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4,c_854])).

tff(c_12,plain,(
    ! [A_5] : k9_relat_1(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_97,plain,(
    ! [A_25,B_26] :
      ( k9_relat_1(k6_relat_1(A_25),B_26) = B_26
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_102,plain,(
    ! [B_27,A_28] :
      ( k9_relat_1(k6_relat_1(B_27),A_28) = A_28
      | ~ r1_tarski(A_28,B_27) ) ),
    inference(resolution,[status(thm)],[c_10,c_97])).

tff(c_111,plain,(
    ! [A_28] :
      ( k9_relat_1(k1_xboole_0,A_28) = A_28
      | ~ r1_tarski(A_28,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_102])).

tff(c_114,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | ~ r1_tarski(A_28,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_111])).

tff(c_873,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_862,c_114])).

tff(c_517,plain,(
    ! [B_105,A_106,A_107] :
      ( k1_xboole_0 = B_105
      | v1_funct_2(A_106,A_107,B_105)
      | k1_relset_1(A_107,B_105,A_106) != A_107
      | ~ r1_tarski(A_106,k2_zfmisc_1(A_107,B_105)) ) ),
    inference(resolution,[status(thm)],[c_10,c_363])).

tff(c_529,plain,(
    ! [A_108] :
      ( k2_relat_1(A_108) = k1_xboole_0
      | v1_funct_2(A_108,k1_relat_1(A_108),k2_relat_1(A_108))
      | k1_relset_1(k1_relat_1(A_108),k2_relat_1(A_108),A_108) != k1_relat_1(A_108)
      | ~ v1_relat_1(A_108) ) ),
    inference(resolution,[status(thm)],[c_14,c_517])).

tff(c_532,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_529,c_95])).

tff(c_535,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_532])).

tff(c_536,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_535])).

tff(c_539,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_536])).

tff(c_543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_539])).

tff(c_544,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_535])).

tff(c_556,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_544,c_14])).

tff(c_564,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4,c_556])).

tff(c_575,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_564,c_114])).

tff(c_122,plain,(
    ! [A_32,B_33,C_34] :
      ( k1_relset_1(A_32,B_33,C_34) = k1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_146,plain,(
    ! [A_43,B_44,A_45] :
      ( k1_relset_1(A_43,B_44,A_45) = k1_relat_1(A_45)
      | ~ r1_tarski(A_45,k2_zfmisc_1(A_43,B_44)) ) ),
    inference(resolution,[status(thm)],[c_10,c_122])).

tff(c_156,plain,(
    ! [A_6] :
      ( k1_relset_1(k1_relat_1(A_6),k2_relat_1(A_6),A_6) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_146])).

tff(c_210,plain,(
    ! [B_61,C_62,A_63] :
      ( k1_xboole_0 = B_61
      | v1_funct_2(C_62,A_63,B_61)
      | k1_relset_1(A_63,B_61,C_62) != A_63
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_223,plain,(
    ! [B_64,A_65,A_66] :
      ( k1_xboole_0 = B_64
      | v1_funct_2(A_65,A_66,B_64)
      | k1_relset_1(A_66,B_64,A_65) != A_66
      | ~ r1_tarski(A_65,k2_zfmisc_1(A_66,B_64)) ) ),
    inference(resolution,[status(thm)],[c_10,c_210])).

tff(c_235,plain,(
    ! [A_67] :
      ( k2_relat_1(A_67) = k1_xboole_0
      | v1_funct_2(A_67,k1_relat_1(A_67),k2_relat_1(A_67))
      | k1_relset_1(k1_relat_1(A_67),k2_relat_1(A_67),A_67) != k1_relat_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(resolution,[status(thm)],[c_14,c_223])).

tff(c_238,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_235,c_95])).

tff(c_241,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_238])).

tff(c_242,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_241])).

tff(c_245,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_242])).

tff(c_249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_245])).

tff(c_250,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_262,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_14])).

tff(c_270,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4,c_262])).

tff(c_281,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_270,c_114])).

tff(c_283,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_270])).

tff(c_22,plain,(
    ! [A_12] :
      ( v1_funct_2(k1_xboole_0,A_12,k1_xboole_0)
      | k1_xboole_0 = A_12
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_12,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_43,plain,(
    ! [A_12] :
      ( v1_funct_2(k1_xboole_0,A_12,k1_xboole_0)
      | k1_xboole_0 = A_12
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_22])).

tff(c_116,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_43])).

tff(c_120,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_116])).

tff(c_299,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_281,c_120])).

tff(c_333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_299])).

tff(c_335,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_376,plain,(
    ! [B_75,C_76] :
      ( k1_relset_1(k1_xboole_0,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_351])).

tff(c_382,plain,(
    ! [B_75] : k1_relset_1(k1_xboole_0,B_75,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_335,c_376])).

tff(c_26,plain,(
    ! [C_14,B_13] :
      ( v1_funct_2(C_14,k1_xboole_0,B_13)
      | k1_relset_1(k1_xboole_0,B_13,C_14) != k1_xboole_0
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_464,plain,(
    ! [C_94,B_95] :
      ( v1_funct_2(C_94,k1_xboole_0,B_95)
      | k1_relset_1(k1_xboole_0,B_95,C_94) != k1_xboole_0
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_26])).

tff(c_466,plain,(
    ! [B_95] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_95)
      | k1_relset_1(k1_xboole_0,B_95,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_335,c_464])).

tff(c_471,plain,(
    ! [B_95] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_95)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_466])).

tff(c_473,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_585,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_575,c_473])).

tff(c_334,plain,(
    ! [A_12] :
      ( v1_funct_2(k1_xboole_0,A_12,k1_xboole_0)
      | k1_xboole_0 = A_12 ) ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_702,plain,(
    ! [A_114] :
      ( v1_funct_2('#skF_1',A_114,'#skF_1')
      | A_114 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_575,c_575,c_334])).

tff(c_546,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_95])).

tff(c_576,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_546])).

tff(c_705,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_702,c_576])).

tff(c_709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_585,c_705])).

tff(c_710,plain,(
    ! [B_95] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_95) ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_885,plain,(
    ! [B_95] : v1_funct_2('#skF_1','#skF_1',B_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_873,c_710])).

tff(c_711,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_886,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_873,c_711])).

tff(c_844,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_842,c_95])).

tff(c_875,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_844])).

tff(c_952,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_886,c_875])).

tff(c_953,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_958,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_10,c_953])).

tff(c_980,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_977,c_958])).

tff(c_984,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_980])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:36:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.44  
% 2.71/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.44  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.71/1.44  
% 2.71/1.44  %Foreground sorts:
% 2.71/1.44  
% 2.71/1.44  
% 2.71/1.44  %Background operators:
% 2.71/1.44  
% 2.71/1.44  
% 2.71/1.44  %Foreground operators:
% 2.71/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.71/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.71/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.71/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.71/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.71/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.71/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.71/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.71/1.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.71/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.71/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.44  
% 2.71/1.46  tff(f_79, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 2.71/1.46  tff(f_41, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 2.71/1.46  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.71/1.46  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.71/1.46  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.71/1.46  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.71/1.46  tff(f_37, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.71/1.46  tff(f_42, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.71/1.46  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 2.71/1.46  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.71/1.46  tff(c_977, plain, (![A_136]: (r1_tarski(A_136, k2_zfmisc_1(k1_relat_1(A_136), k2_relat_1(A_136))) | ~v1_relat_1(A_136))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.71/1.46  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.71/1.46  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.71/1.46  tff(c_14, plain, (![A_6]: (r1_tarski(A_6, k2_zfmisc_1(k1_relat_1(A_6), k2_relat_1(A_6))) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.71/1.46  tff(c_351, plain, (![A_69, B_70, C_71]: (k1_relset_1(A_69, B_70, C_71)=k1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.71/1.46  tff(c_431, plain, (![A_87, B_88, A_89]: (k1_relset_1(A_87, B_88, A_89)=k1_relat_1(A_89) | ~r1_tarski(A_89, k2_zfmisc_1(A_87, B_88)))), inference(resolution, [status(thm)], [c_10, c_351])).
% 2.71/1.46  tff(c_441, plain, (![A_6]: (k1_relset_1(k1_relat_1(A_6), k2_relat_1(A_6), A_6)=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_14, c_431])).
% 2.71/1.46  tff(c_363, plain, (![B_72, C_73, A_74]: (k1_xboole_0=B_72 | v1_funct_2(C_73, A_74, B_72) | k1_relset_1(A_74, B_72, C_73)!=A_74 | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_72))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.71/1.46  tff(c_779, plain, (![B_122, A_123, A_124]: (k1_xboole_0=B_122 | v1_funct_2(A_123, A_124, B_122) | k1_relset_1(A_124, B_122, A_123)!=A_124 | ~r1_tarski(A_123, k2_zfmisc_1(A_124, B_122)))), inference(resolution, [status(thm)], [c_10, c_363])).
% 2.71/1.46  tff(c_822, plain, (![A_130]: (k2_relat_1(A_130)=k1_xboole_0 | v1_funct_2(A_130, k1_relat_1(A_130), k2_relat_1(A_130)) | k1_relset_1(k1_relat_1(A_130), k2_relat_1(A_130), A_130)!=k1_relat_1(A_130) | ~v1_relat_1(A_130))), inference(resolution, [status(thm)], [c_14, c_779])).
% 2.71/1.46  tff(c_36, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.71/1.46  tff(c_34, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.71/1.46  tff(c_40, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34])).
% 2.71/1.46  tff(c_95, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_40])).
% 2.71/1.46  tff(c_825, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_822, c_95])).
% 2.71/1.46  tff(c_831, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_825])).
% 2.71/1.46  tff(c_834, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_831])).
% 2.71/1.46  tff(c_837, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_441, c_834])).
% 2.71/1.46  tff(c_841, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_837])).
% 2.71/1.46  tff(c_842, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_831])).
% 2.71/1.46  tff(c_854, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_842, c_14])).
% 2.71/1.46  tff(c_862, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4, c_854])).
% 2.71/1.46  tff(c_12, plain, (![A_5]: (k9_relat_1(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.71/1.46  tff(c_16, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.71/1.46  tff(c_97, plain, (![A_25, B_26]: (k9_relat_1(k6_relat_1(A_25), B_26)=B_26 | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.71/1.46  tff(c_102, plain, (![B_27, A_28]: (k9_relat_1(k6_relat_1(B_27), A_28)=A_28 | ~r1_tarski(A_28, B_27))), inference(resolution, [status(thm)], [c_10, c_97])).
% 2.71/1.46  tff(c_111, plain, (![A_28]: (k9_relat_1(k1_xboole_0, A_28)=A_28 | ~r1_tarski(A_28, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_102])).
% 2.71/1.46  tff(c_114, plain, (![A_28]: (k1_xboole_0=A_28 | ~r1_tarski(A_28, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_111])).
% 2.71/1.46  tff(c_873, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_862, c_114])).
% 2.71/1.46  tff(c_517, plain, (![B_105, A_106, A_107]: (k1_xboole_0=B_105 | v1_funct_2(A_106, A_107, B_105) | k1_relset_1(A_107, B_105, A_106)!=A_107 | ~r1_tarski(A_106, k2_zfmisc_1(A_107, B_105)))), inference(resolution, [status(thm)], [c_10, c_363])).
% 2.71/1.46  tff(c_529, plain, (![A_108]: (k2_relat_1(A_108)=k1_xboole_0 | v1_funct_2(A_108, k1_relat_1(A_108), k2_relat_1(A_108)) | k1_relset_1(k1_relat_1(A_108), k2_relat_1(A_108), A_108)!=k1_relat_1(A_108) | ~v1_relat_1(A_108))), inference(resolution, [status(thm)], [c_14, c_517])).
% 2.71/1.46  tff(c_532, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_529, c_95])).
% 2.71/1.46  tff(c_535, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_532])).
% 2.71/1.46  tff(c_536, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_535])).
% 2.71/1.46  tff(c_539, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_441, c_536])).
% 2.71/1.46  tff(c_543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_539])).
% 2.71/1.46  tff(c_544, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_535])).
% 2.71/1.46  tff(c_556, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_544, c_14])).
% 2.71/1.46  tff(c_564, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4, c_556])).
% 2.71/1.46  tff(c_575, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_564, c_114])).
% 2.71/1.46  tff(c_122, plain, (![A_32, B_33, C_34]: (k1_relset_1(A_32, B_33, C_34)=k1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.71/1.46  tff(c_146, plain, (![A_43, B_44, A_45]: (k1_relset_1(A_43, B_44, A_45)=k1_relat_1(A_45) | ~r1_tarski(A_45, k2_zfmisc_1(A_43, B_44)))), inference(resolution, [status(thm)], [c_10, c_122])).
% 2.71/1.46  tff(c_156, plain, (![A_6]: (k1_relset_1(k1_relat_1(A_6), k2_relat_1(A_6), A_6)=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_14, c_146])).
% 2.71/1.46  tff(c_210, plain, (![B_61, C_62, A_63]: (k1_xboole_0=B_61 | v1_funct_2(C_62, A_63, B_61) | k1_relset_1(A_63, B_61, C_62)!=A_63 | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_61))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.71/1.46  tff(c_223, plain, (![B_64, A_65, A_66]: (k1_xboole_0=B_64 | v1_funct_2(A_65, A_66, B_64) | k1_relset_1(A_66, B_64, A_65)!=A_66 | ~r1_tarski(A_65, k2_zfmisc_1(A_66, B_64)))), inference(resolution, [status(thm)], [c_10, c_210])).
% 2.71/1.46  tff(c_235, plain, (![A_67]: (k2_relat_1(A_67)=k1_xboole_0 | v1_funct_2(A_67, k1_relat_1(A_67), k2_relat_1(A_67)) | k1_relset_1(k1_relat_1(A_67), k2_relat_1(A_67), A_67)!=k1_relat_1(A_67) | ~v1_relat_1(A_67))), inference(resolution, [status(thm)], [c_14, c_223])).
% 2.71/1.46  tff(c_238, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_235, c_95])).
% 2.71/1.46  tff(c_241, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_238])).
% 2.71/1.46  tff(c_242, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_241])).
% 2.71/1.46  tff(c_245, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_156, c_242])).
% 2.71/1.46  tff(c_249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_245])).
% 2.71/1.46  tff(c_250, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_241])).
% 2.71/1.46  tff(c_262, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_250, c_14])).
% 2.71/1.46  tff(c_270, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4, c_262])).
% 2.71/1.46  tff(c_281, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_270, c_114])).
% 2.71/1.46  tff(c_283, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_281, c_270])).
% 2.71/1.46  tff(c_22, plain, (![A_12]: (v1_funct_2(k1_xboole_0, A_12, k1_xboole_0) | k1_xboole_0=A_12 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_12, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.71/1.46  tff(c_43, plain, (![A_12]: (v1_funct_2(k1_xboole_0, A_12, k1_xboole_0) | k1_xboole_0=A_12 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_22])).
% 2.71/1.46  tff(c_116, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_43])).
% 2.71/1.46  tff(c_120, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_116])).
% 2.71/1.46  tff(c_299, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_281, c_281, c_120])).
% 2.71/1.46  tff(c_333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_283, c_299])).
% 2.71/1.46  tff(c_335, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_43])).
% 2.71/1.46  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.71/1.46  tff(c_376, plain, (![B_75, C_76]: (k1_relset_1(k1_xboole_0, B_75, C_76)=k1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_351])).
% 2.71/1.46  tff(c_382, plain, (![B_75]: (k1_relset_1(k1_xboole_0, B_75, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_335, c_376])).
% 2.71/1.46  tff(c_26, plain, (![C_14, B_13]: (v1_funct_2(C_14, k1_xboole_0, B_13) | k1_relset_1(k1_xboole_0, B_13, C_14)!=k1_xboole_0 | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_13))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.71/1.46  tff(c_464, plain, (![C_94, B_95]: (v1_funct_2(C_94, k1_xboole_0, B_95) | k1_relset_1(k1_xboole_0, B_95, C_94)!=k1_xboole_0 | ~m1_subset_1(C_94, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_26])).
% 2.71/1.46  tff(c_466, plain, (![B_95]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_95) | k1_relset_1(k1_xboole_0, B_95, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_335, c_464])).
% 2.71/1.46  tff(c_471, plain, (![B_95]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_95) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_382, c_466])).
% 2.71/1.46  tff(c_473, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_471])).
% 2.71/1.46  tff(c_585, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_575, c_575, c_473])).
% 2.71/1.46  tff(c_334, plain, (![A_12]: (v1_funct_2(k1_xboole_0, A_12, k1_xboole_0) | k1_xboole_0=A_12)), inference(splitRight, [status(thm)], [c_43])).
% 2.71/1.46  tff(c_702, plain, (![A_114]: (v1_funct_2('#skF_1', A_114, '#skF_1') | A_114='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_575, c_575, c_575, c_334])).
% 2.71/1.46  tff(c_546, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_544, c_95])).
% 2.71/1.46  tff(c_576, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_575, c_546])).
% 2.71/1.46  tff(c_705, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_702, c_576])).
% 2.71/1.46  tff(c_709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_585, c_705])).
% 2.71/1.46  tff(c_710, plain, (![B_95]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_95))), inference(splitRight, [status(thm)], [c_471])).
% 2.71/1.46  tff(c_885, plain, (![B_95]: (v1_funct_2('#skF_1', '#skF_1', B_95))), inference(demodulation, [status(thm), theory('equality')], [c_873, c_873, c_710])).
% 2.71/1.46  tff(c_711, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_471])).
% 2.71/1.46  tff(c_886, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_873, c_873, c_711])).
% 2.71/1.46  tff(c_844, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_842, c_95])).
% 2.71/1.46  tff(c_875, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_873, c_844])).
% 2.71/1.46  tff(c_952, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_885, c_886, c_875])).
% 2.71/1.46  tff(c_953, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_40])).
% 2.71/1.46  tff(c_958, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_953])).
% 2.71/1.46  tff(c_980, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_977, c_958])).
% 2.71/1.46  tff(c_984, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_980])).
% 2.71/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.46  
% 2.71/1.46  Inference rules
% 2.71/1.46  ----------------------
% 2.71/1.46  #Ref     : 0
% 2.71/1.46  #Sup     : 201
% 2.71/1.46  #Fact    : 0
% 2.71/1.46  #Define  : 0
% 2.71/1.46  #Split   : 6
% 2.71/1.46  #Chain   : 0
% 2.71/1.46  #Close   : 0
% 2.71/1.46  
% 2.71/1.46  Ordering : KBO
% 2.71/1.46  
% 2.71/1.46  Simplification rules
% 2.71/1.46  ----------------------
% 2.71/1.46  #Subsume      : 19
% 2.71/1.46  #Demod        : 277
% 2.71/1.46  #Tautology    : 115
% 2.71/1.46  #SimpNegUnit  : 3
% 2.71/1.46  #BackRed      : 90
% 2.71/1.46  
% 2.71/1.46  #Partial instantiations: 0
% 2.71/1.46  #Strategies tried      : 1
% 2.71/1.46  
% 2.71/1.46  Timing (in seconds)
% 2.71/1.46  ----------------------
% 2.71/1.46  Preprocessing        : 0.30
% 2.71/1.46  Parsing              : 0.16
% 2.71/1.46  CNF conversion       : 0.02
% 2.71/1.46  Main loop            : 0.37
% 2.71/1.46  Inferencing          : 0.13
% 2.71/1.46  Reduction            : 0.11
% 2.71/1.46  Demodulation         : 0.08
% 2.71/1.46  BG Simplification    : 0.02
% 2.71/1.46  Subsumption          : 0.07
% 2.71/1.46  Abstraction          : 0.02
% 2.71/1.46  MUC search           : 0.00
% 2.71/1.46  Cooper               : 0.00
% 2.71/1.46  Total                : 0.70
% 2.71/1.46  Index Insertion      : 0.00
% 2.71/1.46  Index Deletion       : 0.00
% 3.09/1.46  Index Matching       : 0.00
% 3.09/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
