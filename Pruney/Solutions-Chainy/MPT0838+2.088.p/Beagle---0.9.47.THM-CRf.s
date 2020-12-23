%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:21 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 396 expanded)
%              Number of leaves         :   30 ( 140 expanded)
%              Depth                    :   13
%              Number of atoms          :  178 ( 835 expanded)
%              Number of equality atoms :   27 ( 114 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_38,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_780,plain,(
    ! [A_148,B_149,C_150] :
      ( k1_relset_1(A_148,B_149,C_150) = k1_relat_1(C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_788,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_780])).

tff(c_30,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_790,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_30])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1('#skF_1'(A_4),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [A_11] :
      ( v1_xboole_0(k1_relat_1(A_11))
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_41,plain,(
    ! [A_44] :
      ( v1_xboole_0(k1_relat_1(A_44))
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    ! [A_45] :
      ( k1_relat_1(A_45) = k1_xboole_0
      | ~ v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_41,c_2])).

tff(c_52,plain,(
    ! [A_47] :
      ( k1_relat_1(k1_relat_1(A_47)) = k1_xboole_0
      | ~ v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_16,c_46])).

tff(c_61,plain,(
    ! [A_47] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_47))
      | ~ v1_xboole_0(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_16])).

tff(c_71,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(k1_relat_1(A_48))
      | ~ v1_xboole_0(A_48) ) ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_78,plain,(
    ! [A_11] : ~ v1_xboole_0(A_11) ),
    inference(resolution,[status(thm)],[c_16,c_71])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_88,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_12])).

tff(c_102,plain,(
    ! [A_55,C_56,B_57] :
      ( m1_subset_1(A_55,C_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(C_56))
      | ~ r2_hidden(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_111,plain,(
    ! [A_59,C_60] :
      ( m1_subset_1(A_59,C_60)
      | ~ r2_hidden(A_59,'#skF_1'(k1_zfmisc_1(C_60))) ) ),
    inference(resolution,[status(thm)],[c_10,c_102])).

tff(c_117,plain,(
    ! [A_61,C_62] :
      ( m1_subset_1(A_61,C_62)
      | ~ m1_subset_1(A_61,'#skF_1'(k1_zfmisc_1(C_62))) ) ),
    inference(resolution,[status(thm)],[c_88,c_111])).

tff(c_140,plain,(
    ! [C_66] : m1_subset_1('#skF_1'('#skF_1'(k1_zfmisc_1(C_66))),C_66) ),
    inference(resolution,[status(thm)],[c_10,c_117])).

tff(c_116,plain,(
    ! [A_6,C_60] :
      ( m1_subset_1(A_6,C_60)
      | ~ m1_subset_1(A_6,'#skF_1'(k1_zfmisc_1(C_60))) ) ),
    inference(resolution,[status(thm)],[c_88,c_111])).

tff(c_172,plain,(
    ! [C_69] : m1_subset_1('#skF_1'('#skF_1'(k1_zfmisc_1('#skF_1'(k1_zfmisc_1(C_69))))),C_69) ),
    inference(resolution,[status(thm)],[c_140,c_116])).

tff(c_123,plain,(
    ! [A_63,B_64,C_65] :
      ( k2_relset_1(A_63,B_64,C_65) = k2_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_131,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_123])).

tff(c_89,plain,(
    ! [A_52,B_53] :
      ( r2_hidden(A_52,B_53)
      | ~ m1_subset_1(A_52,B_53) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_12])).

tff(c_28,plain,(
    ! [D_40] :
      ( ~ r2_hidden(D_40,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_40,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_94,plain,(
    ! [A_52] :
      ( ~ m1_subset_1(A_52,'#skF_3')
      | ~ m1_subset_1(A_52,k2_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_89,c_28])).

tff(c_134,plain,(
    ! [A_52] :
      ( ~ m1_subset_1(A_52,'#skF_3')
      | ~ m1_subset_1(A_52,k2_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_94])).

tff(c_188,plain,(
    ~ m1_subset_1('#skF_1'('#skF_1'(k1_zfmisc_1('#skF_1'(k1_zfmisc_1(k2_relat_1('#skF_4')))))),'#skF_3') ),
    inference(resolution,[status(thm)],[c_172,c_134])).

tff(c_153,plain,(
    ! [C_60] : m1_subset_1('#skF_1'('#skF_1'(k1_zfmisc_1('#skF_1'(k1_zfmisc_1(C_60))))),C_60) ),
    inference(resolution,[status(thm)],[c_140,c_116])).

tff(c_223,plain,(
    ! [A_75,B_76,C_77] :
      ( m1_subset_1(k2_relset_1(A_75,B_76,C_77),k1_zfmisc_1(B_76))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_236,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_223])).

tff(c_241,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_236])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( m1_subset_1(A_8,C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_245,plain,(
    ! [A_78] :
      ( m1_subset_1(A_78,'#skF_3')
      | ~ r2_hidden(A_78,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_241,c_14])).

tff(c_251,plain,(
    ! [A_79] :
      ( m1_subset_1(A_79,'#skF_3')
      | ~ m1_subset_1(A_79,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_88,c_245])).

tff(c_255,plain,(
    m1_subset_1('#skF_1'('#skF_1'(k1_zfmisc_1('#skF_1'(k1_zfmisc_1(k2_relat_1('#skF_4')))))),'#skF_3') ),
    inference(resolution,[status(thm)],[c_153,c_251])).

tff(c_267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_255])).

tff(c_268,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_431,plain,(
    ! [A_108,B_109,C_110] :
      ( k2_relset_1(A_108,B_109,C_110) = k2_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_443,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_431])).

tff(c_299,plain,(
    ! [A_82,B_83] :
      ( r2_hidden(A_82,B_83)
      | v1_xboole_0(B_83)
      | ~ m1_subset_1(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_304,plain,(
    ! [A_82] :
      ( ~ m1_subset_1(A_82,'#skF_3')
      | v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(A_82,k2_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_299,c_28])).

tff(c_308,plain,(
    ! [A_84] :
      ( ~ m1_subset_1(A_84,'#skF_3')
      | ~ m1_subset_1(A_84,k2_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_313,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_308])).

tff(c_445,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_313])).

tff(c_376,plain,(
    ! [A_100,B_101,C_102] :
      ( k1_relset_1(A_100,B_101,C_102) = k1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_389,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_376])).

tff(c_391,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_30])).

tff(c_507,plain,(
    ! [A_118,B_119,C_120] :
      ( m1_subset_1(k2_relset_1(A_118,B_119,C_120),k1_zfmisc_1(B_119))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_527,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_507])).

tff(c_533,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_527])).

tff(c_537,plain,(
    ! [A_121] :
      ( m1_subset_1(A_121,'#skF_3')
      | ~ r2_hidden(A_121,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_533,c_14])).

tff(c_542,plain,(
    ! [A_6] :
      ( m1_subset_1(A_6,'#skF_3')
      | v1_xboole_0(k2_relat_1('#skF_4'))
      | ~ m1_subset_1(A_6,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_12,c_537])).

tff(c_568,plain,(
    v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_542])).

tff(c_582,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_568,c_2])).

tff(c_599,plain,(
    ! [D_124,C_125,B_126,A_127] :
      ( m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(C_125,B_126)))
      | ~ r1_tarski(k2_relat_1(D_124),B_126)
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(C_125,A_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_606,plain,(
    ! [B_126] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_126)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_126) ) ),
    inference(resolution,[status(thm)],[c_32,c_599])).

tff(c_638,plain,(
    ! [B_130] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_130)))
      | ~ r1_tarski(k1_xboole_0,B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_606])).

tff(c_18,plain,(
    ! [C_15,B_13,A_12] :
      ( v1_xboole_0(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(B_13,A_12)))
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_657,plain,(
    ! [B_130] :
      ( v1_xboole_0('#skF_4')
      | ~ v1_xboole_0(B_130)
      | ~ r1_tarski(k1_xboole_0,B_130) ) ),
    inference(resolution,[status(thm)],[c_638,c_18])).

tff(c_685,plain,(
    ! [B_134] :
      ( ~ v1_xboole_0(B_134)
      | ~ r1_tarski(k1_xboole_0,B_134) ) ),
    inference(splitLeft,[status(thm)],[c_657])).

tff(c_689,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_685])).

tff(c_693,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_689])).

tff(c_694,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_657])).

tff(c_45,plain,(
    ! [A_44] :
      ( k1_relat_1(A_44) = k1_xboole_0
      | ~ v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_41,c_2])).

tff(c_701,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_694,c_45])).

tff(c_710,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_391,c_701])).

tff(c_713,plain,(
    ! [A_135] :
      ( m1_subset_1(A_135,'#skF_3')
      | ~ m1_subset_1(A_135,k2_relat_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_542])).

tff(c_717,plain,(
    m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_713])).

tff(c_721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_445,c_717])).

tff(c_722,plain,(
    v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_730,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_722,c_2])).

tff(c_838,plain,(
    ! [A_157,B_158,C_159] :
      ( k2_relset_1(A_157,B_158,C_159) = k2_relat_1(C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_844,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_838])).

tff(c_851,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_844])).

tff(c_961,plain,(
    ! [D_172,C_173,B_174,A_175] :
      ( m1_subset_1(D_172,k1_zfmisc_1(k2_zfmisc_1(C_173,B_174)))
      | ~ r1_tarski(k2_relat_1(D_172),B_174)
      | ~ m1_subset_1(D_172,k1_zfmisc_1(k2_zfmisc_1(C_173,A_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_968,plain,(
    ! [B_174] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_174)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_174) ) ),
    inference(resolution,[status(thm)],[c_32,c_961])).

tff(c_977,plain,(
    ! [B_176] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_176)))
      | ~ r1_tarski(k1_xboole_0,B_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_851,c_968])).

tff(c_996,plain,(
    ! [B_176] :
      ( v1_xboole_0('#skF_4')
      | ~ v1_xboole_0(B_176)
      | ~ r1_tarski(k1_xboole_0,B_176) ) ),
    inference(resolution,[status(thm)],[c_977,c_18])).

tff(c_999,plain,(
    ! [B_177] :
      ( ~ v1_xboole_0(B_177)
      | ~ r1_tarski(k1_xboole_0,B_177) ) ),
    inference(splitLeft,[status(thm)],[c_996])).

tff(c_1003,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_999])).

tff(c_1007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_1003])).

tff(c_1008,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_996])).

tff(c_1021,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1008,c_45])).

tff(c_1030,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_790,c_1021])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:12:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.45  
% 2.95/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.45  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.95/1.45  
% 2.95/1.45  %Foreground sorts:
% 2.95/1.45  
% 2.95/1.45  
% 2.95/1.45  %Background operators:
% 2.95/1.45  
% 2.95/1.45  
% 2.95/1.45  %Foreground operators:
% 2.95/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.95/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.95/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.95/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.95/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.95/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.95/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.95/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.95/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.45  
% 2.95/1.47  tff(f_100, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 2.95/1.47  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.95/1.47  tff(f_38, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.95/1.47  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.95/1.47  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.95/1.47  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.95/1.47  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.95/1.47  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.95/1.47  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.95/1.47  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.95/1.47  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 2.95/1.47  tff(f_61, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.95/1.47  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.95/1.47  tff(c_780, plain, (![A_148, B_149, C_150]: (k1_relset_1(A_148, B_149, C_150)=k1_relat_1(C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.95/1.47  tff(c_788, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_780])).
% 2.95/1.47  tff(c_30, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.95/1.47  tff(c_790, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_788, c_30])).
% 2.95/1.47  tff(c_10, plain, (![A_4]: (m1_subset_1('#skF_1'(A_4), A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.95/1.47  tff(c_16, plain, (![A_11]: (v1_xboole_0(k1_relat_1(A_11)) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.95/1.47  tff(c_41, plain, (![A_44]: (v1_xboole_0(k1_relat_1(A_44)) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.95/1.47  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.95/1.47  tff(c_46, plain, (![A_45]: (k1_relat_1(A_45)=k1_xboole_0 | ~v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_41, c_2])).
% 2.95/1.47  tff(c_52, plain, (![A_47]: (k1_relat_1(k1_relat_1(A_47))=k1_xboole_0 | ~v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_16, c_46])).
% 2.95/1.47  tff(c_61, plain, (![A_47]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_47)) | ~v1_xboole_0(A_47))), inference(superposition, [status(thm), theory('equality')], [c_52, c_16])).
% 2.95/1.47  tff(c_71, plain, (![A_48]: (~v1_xboole_0(k1_relat_1(A_48)) | ~v1_xboole_0(A_48))), inference(splitLeft, [status(thm)], [c_61])).
% 2.95/1.47  tff(c_78, plain, (![A_11]: (~v1_xboole_0(A_11))), inference(resolution, [status(thm)], [c_16, c_71])).
% 2.95/1.47  tff(c_12, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.95/1.47  tff(c_88, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | ~m1_subset_1(A_6, B_7))), inference(negUnitSimplification, [status(thm)], [c_78, c_12])).
% 2.95/1.47  tff(c_102, plain, (![A_55, C_56, B_57]: (m1_subset_1(A_55, C_56) | ~m1_subset_1(B_57, k1_zfmisc_1(C_56)) | ~r2_hidden(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.95/1.47  tff(c_111, plain, (![A_59, C_60]: (m1_subset_1(A_59, C_60) | ~r2_hidden(A_59, '#skF_1'(k1_zfmisc_1(C_60))))), inference(resolution, [status(thm)], [c_10, c_102])).
% 2.95/1.47  tff(c_117, plain, (![A_61, C_62]: (m1_subset_1(A_61, C_62) | ~m1_subset_1(A_61, '#skF_1'(k1_zfmisc_1(C_62))))), inference(resolution, [status(thm)], [c_88, c_111])).
% 2.95/1.47  tff(c_140, plain, (![C_66]: (m1_subset_1('#skF_1'('#skF_1'(k1_zfmisc_1(C_66))), C_66))), inference(resolution, [status(thm)], [c_10, c_117])).
% 2.95/1.47  tff(c_116, plain, (![A_6, C_60]: (m1_subset_1(A_6, C_60) | ~m1_subset_1(A_6, '#skF_1'(k1_zfmisc_1(C_60))))), inference(resolution, [status(thm)], [c_88, c_111])).
% 2.95/1.47  tff(c_172, plain, (![C_69]: (m1_subset_1('#skF_1'('#skF_1'(k1_zfmisc_1('#skF_1'(k1_zfmisc_1(C_69))))), C_69))), inference(resolution, [status(thm)], [c_140, c_116])).
% 2.95/1.47  tff(c_123, plain, (![A_63, B_64, C_65]: (k2_relset_1(A_63, B_64, C_65)=k2_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.95/1.47  tff(c_131, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_123])).
% 2.95/1.47  tff(c_89, plain, (![A_52, B_53]: (r2_hidden(A_52, B_53) | ~m1_subset_1(A_52, B_53))), inference(negUnitSimplification, [status(thm)], [c_78, c_12])).
% 2.95/1.47  tff(c_28, plain, (![D_40]: (~r2_hidden(D_40, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_40, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.95/1.47  tff(c_94, plain, (![A_52]: (~m1_subset_1(A_52, '#skF_3') | ~m1_subset_1(A_52, k2_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_89, c_28])).
% 2.95/1.47  tff(c_134, plain, (![A_52]: (~m1_subset_1(A_52, '#skF_3') | ~m1_subset_1(A_52, k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_94])).
% 2.95/1.47  tff(c_188, plain, (~m1_subset_1('#skF_1'('#skF_1'(k1_zfmisc_1('#skF_1'(k1_zfmisc_1(k2_relat_1('#skF_4')))))), '#skF_3')), inference(resolution, [status(thm)], [c_172, c_134])).
% 2.95/1.47  tff(c_153, plain, (![C_60]: (m1_subset_1('#skF_1'('#skF_1'(k1_zfmisc_1('#skF_1'(k1_zfmisc_1(C_60))))), C_60))), inference(resolution, [status(thm)], [c_140, c_116])).
% 2.95/1.47  tff(c_223, plain, (![A_75, B_76, C_77]: (m1_subset_1(k2_relset_1(A_75, B_76, C_77), k1_zfmisc_1(B_76)) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.95/1.47  tff(c_236, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_131, c_223])).
% 2.95/1.47  tff(c_241, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_236])).
% 2.95/1.47  tff(c_14, plain, (![A_8, C_10, B_9]: (m1_subset_1(A_8, C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.95/1.47  tff(c_245, plain, (![A_78]: (m1_subset_1(A_78, '#skF_3') | ~r2_hidden(A_78, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_241, c_14])).
% 2.95/1.47  tff(c_251, plain, (![A_79]: (m1_subset_1(A_79, '#skF_3') | ~m1_subset_1(A_79, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_88, c_245])).
% 2.95/1.47  tff(c_255, plain, (m1_subset_1('#skF_1'('#skF_1'(k1_zfmisc_1('#skF_1'(k1_zfmisc_1(k2_relat_1('#skF_4')))))), '#skF_3')), inference(resolution, [status(thm)], [c_153, c_251])).
% 2.95/1.47  tff(c_267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_255])).
% 2.95/1.47  tff(c_268, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_61])).
% 2.95/1.47  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.95/1.47  tff(c_431, plain, (![A_108, B_109, C_110]: (k2_relset_1(A_108, B_109, C_110)=k2_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.95/1.47  tff(c_443, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_431])).
% 2.95/1.47  tff(c_299, plain, (![A_82, B_83]: (r2_hidden(A_82, B_83) | v1_xboole_0(B_83) | ~m1_subset_1(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.95/1.47  tff(c_304, plain, (![A_82]: (~m1_subset_1(A_82, '#skF_3') | v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(A_82, k2_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_299, c_28])).
% 2.95/1.47  tff(c_308, plain, (![A_84]: (~m1_subset_1(A_84, '#skF_3') | ~m1_subset_1(A_84, k2_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_304])).
% 2.95/1.47  tff(c_313, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_10, c_308])).
% 2.95/1.47  tff(c_445, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_443, c_313])).
% 2.95/1.47  tff(c_376, plain, (![A_100, B_101, C_102]: (k1_relset_1(A_100, B_101, C_102)=k1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.95/1.47  tff(c_389, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_376])).
% 2.95/1.47  tff(c_391, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_389, c_30])).
% 2.95/1.47  tff(c_507, plain, (![A_118, B_119, C_120]: (m1_subset_1(k2_relset_1(A_118, B_119, C_120), k1_zfmisc_1(B_119)) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.95/1.47  tff(c_527, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_443, c_507])).
% 2.95/1.47  tff(c_533, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_527])).
% 2.95/1.47  tff(c_537, plain, (![A_121]: (m1_subset_1(A_121, '#skF_3') | ~r2_hidden(A_121, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_533, c_14])).
% 2.95/1.47  tff(c_542, plain, (![A_6]: (m1_subset_1(A_6, '#skF_3') | v1_xboole_0(k2_relat_1('#skF_4')) | ~m1_subset_1(A_6, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_12, c_537])).
% 2.95/1.47  tff(c_568, plain, (v1_xboole_0(k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_542])).
% 2.95/1.47  tff(c_582, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_568, c_2])).
% 2.95/1.47  tff(c_599, plain, (![D_124, C_125, B_126, A_127]: (m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(C_125, B_126))) | ~r1_tarski(k2_relat_1(D_124), B_126) | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(C_125, A_127))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.95/1.47  tff(c_606, plain, (![B_126]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_126))) | ~r1_tarski(k2_relat_1('#skF_4'), B_126))), inference(resolution, [status(thm)], [c_32, c_599])).
% 2.95/1.47  tff(c_638, plain, (![B_130]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_130))) | ~r1_tarski(k1_xboole_0, B_130))), inference(demodulation, [status(thm), theory('equality')], [c_582, c_606])).
% 2.95/1.47  tff(c_18, plain, (![C_15, B_13, A_12]: (v1_xboole_0(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(B_13, A_12))) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.95/1.47  tff(c_657, plain, (![B_130]: (v1_xboole_0('#skF_4') | ~v1_xboole_0(B_130) | ~r1_tarski(k1_xboole_0, B_130))), inference(resolution, [status(thm)], [c_638, c_18])).
% 2.95/1.47  tff(c_685, plain, (![B_134]: (~v1_xboole_0(B_134) | ~r1_tarski(k1_xboole_0, B_134))), inference(splitLeft, [status(thm)], [c_657])).
% 2.95/1.47  tff(c_689, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_685])).
% 2.95/1.47  tff(c_693, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_268, c_689])).
% 2.95/1.47  tff(c_694, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_657])).
% 2.95/1.47  tff(c_45, plain, (![A_44]: (k1_relat_1(A_44)=k1_xboole_0 | ~v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_41, c_2])).
% 2.95/1.47  tff(c_701, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_694, c_45])).
% 2.95/1.47  tff(c_710, plain, $false, inference(negUnitSimplification, [status(thm)], [c_391, c_701])).
% 2.95/1.47  tff(c_713, plain, (![A_135]: (m1_subset_1(A_135, '#skF_3') | ~m1_subset_1(A_135, k2_relat_1('#skF_4')))), inference(splitRight, [status(thm)], [c_542])).
% 2.95/1.47  tff(c_717, plain, (m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_10, c_713])).
% 2.95/1.47  tff(c_721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_445, c_717])).
% 2.95/1.47  tff(c_722, plain, (v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_304])).
% 2.95/1.47  tff(c_730, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_722, c_2])).
% 2.95/1.47  tff(c_838, plain, (![A_157, B_158, C_159]: (k2_relset_1(A_157, B_158, C_159)=k2_relat_1(C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.95/1.47  tff(c_844, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_838])).
% 2.95/1.47  tff(c_851, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_730, c_844])).
% 2.95/1.47  tff(c_961, plain, (![D_172, C_173, B_174, A_175]: (m1_subset_1(D_172, k1_zfmisc_1(k2_zfmisc_1(C_173, B_174))) | ~r1_tarski(k2_relat_1(D_172), B_174) | ~m1_subset_1(D_172, k1_zfmisc_1(k2_zfmisc_1(C_173, A_175))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.95/1.47  tff(c_968, plain, (![B_174]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_174))) | ~r1_tarski(k2_relat_1('#skF_4'), B_174))), inference(resolution, [status(thm)], [c_32, c_961])).
% 2.95/1.47  tff(c_977, plain, (![B_176]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_176))) | ~r1_tarski(k1_xboole_0, B_176))), inference(demodulation, [status(thm), theory('equality')], [c_851, c_968])).
% 2.95/1.47  tff(c_996, plain, (![B_176]: (v1_xboole_0('#skF_4') | ~v1_xboole_0(B_176) | ~r1_tarski(k1_xboole_0, B_176))), inference(resolution, [status(thm)], [c_977, c_18])).
% 2.95/1.47  tff(c_999, plain, (![B_177]: (~v1_xboole_0(B_177) | ~r1_tarski(k1_xboole_0, B_177))), inference(splitLeft, [status(thm)], [c_996])).
% 2.95/1.47  tff(c_1003, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_999])).
% 2.95/1.47  tff(c_1007, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_268, c_1003])).
% 2.95/1.47  tff(c_1008, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_996])).
% 2.95/1.47  tff(c_1021, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1008, c_45])).
% 2.95/1.47  tff(c_1030, plain, $false, inference(negUnitSimplification, [status(thm)], [c_790, c_1021])).
% 2.95/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.47  
% 2.95/1.47  Inference rules
% 2.95/1.47  ----------------------
% 2.95/1.47  #Ref     : 0
% 2.95/1.47  #Sup     : 219
% 2.95/1.47  #Fact    : 0
% 2.95/1.47  #Define  : 0
% 2.95/1.47  #Split   : 6
% 2.95/1.47  #Chain   : 0
% 2.95/1.47  #Close   : 0
% 2.95/1.47  
% 2.95/1.47  Ordering : KBO
% 2.95/1.47  
% 2.95/1.47  Simplification rules
% 2.95/1.47  ----------------------
% 2.95/1.47  #Subsume      : 21
% 2.95/1.47  #Demod        : 80
% 2.95/1.47  #Tautology    : 84
% 2.95/1.47  #SimpNegUnit  : 7
% 2.95/1.47  #BackRed      : 18
% 2.95/1.47  
% 2.95/1.47  #Partial instantiations: 0
% 2.95/1.47  #Strategies tried      : 1
% 2.95/1.47  
% 2.95/1.47  Timing (in seconds)
% 2.95/1.47  ----------------------
% 3.12/1.48  Preprocessing        : 0.30
% 3.12/1.48  Parsing              : 0.15
% 3.12/1.48  CNF conversion       : 0.02
% 3.12/1.48  Main loop            : 0.39
% 3.12/1.48  Inferencing          : 0.15
% 3.12/1.48  Reduction            : 0.11
% 3.12/1.48  Demodulation         : 0.08
% 3.12/1.48  BG Simplification    : 0.02
% 3.12/1.48  Subsumption          : 0.07
% 3.12/1.48  Abstraction          : 0.02
% 3.12/1.48  MUC search           : 0.00
% 3.12/1.48  Cooper               : 0.00
% 3.12/1.48  Total                : 0.73
% 3.12/1.48  Index Insertion      : 0.00
% 3.12/1.48  Index Deletion       : 0.00
% 3.12/1.48  Index Matching       : 0.00
% 3.12/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
