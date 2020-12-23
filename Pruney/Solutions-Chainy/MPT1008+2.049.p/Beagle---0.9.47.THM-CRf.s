%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:32 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 164 expanded)
%              Number of leaves         :   42 (  73 expanded)
%              Depth                    :   13
%              Number of atoms          :  146 ( 327 expanded)
%              Number of equality atoms :   61 ( 136 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_66,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_73,plain,(
    ! [A_42] : k2_tarski(A_42,A_42) = k1_tarski(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_12,B_13] : ~ v1_xboole_0(k2_tarski(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_78,plain,(
    ! [A_42] : ~ v1_xboole_0(k1_tarski(A_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_14])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_131,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_135,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_131])).

tff(c_36,plain,(
    ! [A_19] :
      ( k1_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_142,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_135,c_36])).

tff(c_144,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_201,plain,(
    ! [B_79,A_80] :
      ( k1_tarski(k1_funct_1(B_79,A_80)) = k2_relat_1(B_79)
      | k1_tarski(A_80) != k1_relat_1(B_79)
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_191,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_195,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_191])).

tff(c_52,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_196,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_52])).

tff(c_207,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_196])).

tff(c_228,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_60,c_207])).

tff(c_153,plain,(
    ! [C_64,A_65,B_66] :
      ( v4_relat_1(C_64,A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_157,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_153])).

tff(c_28,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_235,plain,(
    ! [B_83,C_84,A_85] :
      ( k2_tarski(B_83,C_84) = A_85
      | k1_tarski(C_84) = A_85
      | k1_tarski(B_83) = A_85
      | k1_xboole_0 = A_85
      | ~ r1_tarski(A_85,k2_tarski(B_83,C_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_251,plain,(
    ! [A_6,A_85] :
      ( k2_tarski(A_6,A_6) = A_85
      | k1_tarski(A_6) = A_85
      | k1_tarski(A_6) = A_85
      | k1_xboole_0 = A_85
      | ~ r1_tarski(A_85,k1_tarski(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_235])).

tff(c_266,plain,(
    ! [A_86,A_87] :
      ( k1_tarski(A_86) = A_87
      | k1_tarski(A_86) = A_87
      | k1_tarski(A_86) = A_87
      | k1_xboole_0 = A_87
      | ~ r1_tarski(A_87,k1_tarski(A_86)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_251])).

tff(c_286,plain,(
    ! [A_88,B_89] :
      ( k1_tarski(A_88) = k1_relat_1(B_89)
      | k1_relat_1(B_89) = k1_xboole_0
      | ~ v4_relat_1(B_89,k1_tarski(A_88))
      | ~ v1_relat_1(B_89) ) ),
    inference(resolution,[status(thm)],[c_28,c_266])).

tff(c_292,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_157,c_286])).

tff(c_295,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_292])).

tff(c_297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_228,c_295])).

tff(c_298,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_303,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_6])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_306,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_54])).

tff(c_58,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_305,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_298,c_30])).

tff(c_401,plain,(
    ! [A_108,B_109,C_110] :
      ( k2_relset_1(A_108,B_109,C_110) = k2_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_404,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_401])).

tff(c_406,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_404])).

tff(c_50,plain,(
    ! [D_36,C_35,A_33,B_34] :
      ( r2_hidden(k1_funct_1(D_36,C_35),k2_relset_1(A_33,B_34,D_36))
      | k1_xboole_0 = B_34
      | ~ r2_hidden(C_35,A_33)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_2(D_36,A_33,B_34)
      | ~ v1_funct_1(D_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_507,plain,(
    ! [D_125,C_126,A_127,B_128] :
      ( r2_hidden(k1_funct_1(D_125,C_126),k2_relset_1(A_127,B_128,D_125))
      | B_128 = '#skF_4'
      | ~ r2_hidden(C_126,A_127)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128)))
      | ~ v1_funct_2(D_125,A_127,B_128)
      | ~ v1_funct_1(D_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_50])).

tff(c_516,plain,(
    ! [C_126] :
      ( r2_hidden(k1_funct_1('#skF_4',C_126),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_126,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_507])).

tff(c_520,plain,(
    ! [C_126] :
      ( r2_hidden(k1_funct_1('#skF_4',C_126),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_126,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_516])).

tff(c_522,plain,(
    ! [C_129] :
      ( r2_hidden(k1_funct_1('#skF_4',C_129),'#skF_4')
      | ~ r2_hidden(C_129,k1_tarski('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_520])).

tff(c_40,plain,(
    ! [B_23,A_22] :
      ( ~ r1_tarski(B_23,A_22)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_525,plain,(
    ! [C_129] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_4',C_129))
      | ~ r2_hidden(C_129,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_522,c_40])).

tff(c_535,plain,(
    ! [C_130] : ~ r2_hidden(C_130,k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_525])).

tff(c_539,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_535])).

tff(c_543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_539])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n014.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 17:10:37 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.33  
% 2.69/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.33  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.69/1.33  
% 2.69/1.33  %Foreground sorts:
% 2.69/1.33  
% 2.69/1.33  
% 2.69/1.33  %Background operators:
% 2.69/1.33  
% 2.69/1.33  
% 2.69/1.33  %Foreground operators:
% 2.69/1.33  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.69/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.69/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.69/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.69/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.69/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.69/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.69/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.69/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.69/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.69/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.69/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.69/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.69/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.69/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.69/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.33  
% 2.69/1.35  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.69/1.35  tff(f_42, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_xboole_0)).
% 2.69/1.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.69/1.35  tff(f_125, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 2.69/1.35  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.69/1.35  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.69/1.35  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.69/1.35  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.69/1.35  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.69/1.35  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.69/1.35  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.69/1.35  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.69/1.35  tff(f_66, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.69/1.35  tff(f_113, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 2.69/1.35  tff(f_87, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.69/1.35  tff(c_73, plain, (![A_42]: (k2_tarski(A_42, A_42)=k1_tarski(A_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.69/1.35  tff(c_14, plain, (![A_12, B_13]: (~v1_xboole_0(k2_tarski(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.69/1.35  tff(c_78, plain, (![A_42]: (~v1_xboole_0(k1_tarski(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_73, c_14])).
% 2.69/1.35  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.35  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.69/1.35  tff(c_131, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.69/1.35  tff(c_135, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_131])).
% 2.69/1.35  tff(c_36, plain, (![A_19]: (k1_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.69/1.35  tff(c_142, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_135, c_36])).
% 2.69/1.35  tff(c_144, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_142])).
% 2.69/1.35  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.69/1.35  tff(c_201, plain, (![B_79, A_80]: (k1_tarski(k1_funct_1(B_79, A_80))=k2_relat_1(B_79) | k1_tarski(A_80)!=k1_relat_1(B_79) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.69/1.35  tff(c_191, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.69/1.35  tff(c_195, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_191])).
% 2.69/1.35  tff(c_52, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.69/1.35  tff(c_196, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_52])).
% 2.69/1.35  tff(c_207, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_201, c_196])).
% 2.69/1.35  tff(c_228, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_60, c_207])).
% 2.69/1.35  tff(c_153, plain, (![C_64, A_65, B_66]: (v4_relat_1(C_64, A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.69/1.35  tff(c_157, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_153])).
% 2.69/1.35  tff(c_28, plain, (![B_18, A_17]: (r1_tarski(k1_relat_1(B_18), A_17) | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.69/1.35  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.69/1.35  tff(c_235, plain, (![B_83, C_84, A_85]: (k2_tarski(B_83, C_84)=A_85 | k1_tarski(C_84)=A_85 | k1_tarski(B_83)=A_85 | k1_xboole_0=A_85 | ~r1_tarski(A_85, k2_tarski(B_83, C_84)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.69/1.35  tff(c_251, plain, (![A_6, A_85]: (k2_tarski(A_6, A_6)=A_85 | k1_tarski(A_6)=A_85 | k1_tarski(A_6)=A_85 | k1_xboole_0=A_85 | ~r1_tarski(A_85, k1_tarski(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_235])).
% 2.69/1.35  tff(c_266, plain, (![A_86, A_87]: (k1_tarski(A_86)=A_87 | k1_tarski(A_86)=A_87 | k1_tarski(A_86)=A_87 | k1_xboole_0=A_87 | ~r1_tarski(A_87, k1_tarski(A_86)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_251])).
% 2.69/1.35  tff(c_286, plain, (![A_88, B_89]: (k1_tarski(A_88)=k1_relat_1(B_89) | k1_relat_1(B_89)=k1_xboole_0 | ~v4_relat_1(B_89, k1_tarski(A_88)) | ~v1_relat_1(B_89))), inference(resolution, [status(thm)], [c_28, c_266])).
% 2.69/1.35  tff(c_292, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_157, c_286])).
% 2.69/1.35  tff(c_295, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_135, c_292])).
% 2.69/1.35  tff(c_297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_228, c_295])).
% 2.69/1.35  tff(c_298, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_142])).
% 2.69/1.35  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.69/1.35  tff(c_303, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_298, c_6])).
% 2.69/1.35  tff(c_54, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.69/1.35  tff(c_306, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_298, c_54])).
% 2.69/1.35  tff(c_58, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.69/1.35  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.69/1.35  tff(c_305, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_298, c_298, c_30])).
% 2.69/1.35  tff(c_401, plain, (![A_108, B_109, C_110]: (k2_relset_1(A_108, B_109, C_110)=k2_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.69/1.35  tff(c_404, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_401])).
% 2.69/1.35  tff(c_406, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_305, c_404])).
% 2.69/1.35  tff(c_50, plain, (![D_36, C_35, A_33, B_34]: (r2_hidden(k1_funct_1(D_36, C_35), k2_relset_1(A_33, B_34, D_36)) | k1_xboole_0=B_34 | ~r2_hidden(C_35, A_33) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_2(D_36, A_33, B_34) | ~v1_funct_1(D_36))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.69/1.35  tff(c_507, plain, (![D_125, C_126, A_127, B_128]: (r2_hidden(k1_funct_1(D_125, C_126), k2_relset_1(A_127, B_128, D_125)) | B_128='#skF_4' | ~r2_hidden(C_126, A_127) | ~m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))) | ~v1_funct_2(D_125, A_127, B_128) | ~v1_funct_1(D_125))), inference(demodulation, [status(thm), theory('equality')], [c_298, c_50])).
% 2.69/1.35  tff(c_516, plain, (![C_126]: (r2_hidden(k1_funct_1('#skF_4', C_126), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_126, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_406, c_507])).
% 2.69/1.35  tff(c_520, plain, (![C_126]: (r2_hidden(k1_funct_1('#skF_4', C_126), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_126, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_516])).
% 2.69/1.35  tff(c_522, plain, (![C_129]: (r2_hidden(k1_funct_1('#skF_4', C_129), '#skF_4') | ~r2_hidden(C_129, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_306, c_520])).
% 2.69/1.35  tff(c_40, plain, (![B_23, A_22]: (~r1_tarski(B_23, A_22) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.69/1.35  tff(c_525, plain, (![C_129]: (~r1_tarski('#skF_4', k1_funct_1('#skF_4', C_129)) | ~r2_hidden(C_129, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_522, c_40])).
% 2.69/1.35  tff(c_535, plain, (![C_130]: (~r2_hidden(C_130, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_303, c_525])).
% 2.69/1.35  tff(c_539, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_4, c_535])).
% 2.69/1.35  tff(c_543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_539])).
% 2.69/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.35  
% 2.69/1.35  Inference rules
% 2.69/1.35  ----------------------
% 2.69/1.35  #Ref     : 0
% 2.69/1.35  #Sup     : 101
% 2.69/1.35  #Fact    : 0
% 2.69/1.35  #Define  : 0
% 2.69/1.35  #Split   : 3
% 2.69/1.35  #Chain   : 0
% 2.69/1.35  #Close   : 0
% 2.69/1.35  
% 2.69/1.35  Ordering : KBO
% 2.69/1.35  
% 2.69/1.35  Simplification rules
% 2.69/1.35  ----------------------
% 2.69/1.35  #Subsume      : 8
% 2.69/1.35  #Demod        : 73
% 2.69/1.35  #Tautology    : 52
% 2.69/1.35  #SimpNegUnit  : 6
% 2.69/1.35  #BackRed      : 9
% 2.69/1.35  
% 2.69/1.35  #Partial instantiations: 0
% 2.69/1.35  #Strategies tried      : 1
% 2.69/1.35  
% 2.69/1.35  Timing (in seconds)
% 2.69/1.35  ----------------------
% 2.69/1.35  Preprocessing        : 0.33
% 2.69/1.35  Parsing              : 0.17
% 2.69/1.35  CNF conversion       : 0.02
% 2.69/1.35  Main loop            : 0.28
% 2.69/1.35  Inferencing          : 0.10
% 2.69/1.35  Reduction            : 0.09
% 2.69/1.35  Demodulation         : 0.06
% 2.69/1.35  BG Simplification    : 0.02
% 2.69/1.36  Subsumption          : 0.05
% 2.69/1.36  Abstraction          : 0.01
% 2.69/1.36  MUC search           : 0.00
% 2.69/1.36  Cooper               : 0.00
% 2.69/1.36  Total                : 0.64
% 2.69/1.36  Index Insertion      : 0.00
% 2.69/1.36  Index Deletion       : 0.00
% 2.69/1.36  Index Matching       : 0.00
% 2.69/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
