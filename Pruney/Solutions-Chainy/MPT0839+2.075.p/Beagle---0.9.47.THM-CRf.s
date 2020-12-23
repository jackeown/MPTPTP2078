%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:31 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 339 expanded)
%              Number of leaves         :   30 ( 122 expanded)
%              Depth                    :   14
%              Number of atoms          :  174 ( 708 expanded)
%              Number of equality atoms :   26 (  94 expanded)
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
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_38,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_873,plain,(
    ! [A_155,B_156,C_157] :
      ( k2_relset_1(A_155,B_156,C_157) = k2_relat_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_886,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_873])).

tff(c_30,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_888,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_30])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1('#skF_1'(A_4),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [A_11] :
      ( v1_xboole_0(k2_relat_1(A_11))
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_41,plain,(
    ! [A_44] :
      ( v1_xboole_0(k2_relat_1(A_44))
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    ! [A_45] :
      ( k2_relat_1(A_45) = k1_xboole_0
      | ~ v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_41,c_2])).

tff(c_52,plain,(
    ! [A_47] :
      ( k2_relat_1(k2_relat_1(A_47)) = k1_xboole_0
      | ~ v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_16,c_46])).

tff(c_61,plain,(
    ! [A_47] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k2_relat_1(A_47))
      | ~ v1_xboole_0(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_16])).

tff(c_71,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(k2_relat_1(A_48))
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

tff(c_138,plain,(
    ! [C_66] : m1_subset_1('#skF_1'('#skF_1'(k1_zfmisc_1(C_66))),C_66) ),
    inference(resolution,[status(thm)],[c_10,c_117])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( m1_subset_1(A_8,C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_178,plain,(
    ! [A_68,C_69] :
      ( m1_subset_1(A_68,C_69)
      | ~ r2_hidden(A_68,'#skF_1'('#skF_1'(k1_zfmisc_1(k1_zfmisc_1(C_69))))) ) ),
    inference(resolution,[status(thm)],[c_138,c_14])).

tff(c_204,plain,(
    ! [A_71,C_72] :
      ( m1_subset_1(A_71,C_72)
      | ~ m1_subset_1(A_71,'#skF_1'('#skF_1'(k1_zfmisc_1(k1_zfmisc_1(C_72))))) ) ),
    inference(resolution,[status(thm)],[c_88,c_178])).

tff(c_224,plain,(
    ! [C_72] : m1_subset_1('#skF_1'('#skF_1'('#skF_1'(k1_zfmisc_1(k1_zfmisc_1(C_72))))),C_72) ),
    inference(resolution,[status(thm)],[c_10,c_204])).

tff(c_250,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_278,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_250])).

tff(c_89,plain,(
    ! [A_52,B_53] :
      ( r2_hidden(A_52,B_53)
      | ~ m1_subset_1(A_52,B_53) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_12])).

tff(c_28,plain,(
    ! [D_40] :
      ( ~ r2_hidden(D_40,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_40,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_94,plain,(
    ! [A_52] :
      ( ~ m1_subset_1(A_52,'#skF_3')
      | ~ m1_subset_1(A_52,k1_relset_1('#skF_3','#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_89,c_28])).

tff(c_294,plain,(
    ! [A_78] :
      ( ~ m1_subset_1(A_78,'#skF_3')
      | ~ m1_subset_1(A_78,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_94])).

tff(c_315,plain,(
    ~ m1_subset_1('#skF_1'('#skF_1'('#skF_1'(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4')))))),'#skF_3') ),
    inference(resolution,[status(thm)],[c_224,c_294])).

tff(c_320,plain,(
    ! [A_79,B_80,C_81] :
      ( m1_subset_1(k1_relset_1(A_79,B_80,C_81),k1_zfmisc_1(A_79))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_333,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_320])).

tff(c_338,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_333])).

tff(c_342,plain,(
    ! [A_82] :
      ( m1_subset_1(A_82,'#skF_3')
      | ~ r2_hidden(A_82,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_338,c_14])).

tff(c_348,plain,(
    ! [A_83] :
      ( m1_subset_1(A_83,'#skF_3')
      | ~ m1_subset_1(A_83,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_88,c_342])).

tff(c_352,plain,(
    m1_subset_1('#skF_1'('#skF_1'('#skF_1'(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4')))))),'#skF_3') ),
    inference(resolution,[status(thm)],[c_224,c_348])).

tff(c_372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_352])).

tff(c_373,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_481,plain,(
    ! [A_104,B_105,C_106] :
      ( k2_relset_1(A_104,B_105,C_106) = k2_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_494,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_481])).

tff(c_496,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_30])).

tff(c_511,plain,(
    ! [A_109,B_110,C_111] :
      ( k1_relset_1(A_109,B_110,C_111) = k1_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_523,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_511])).

tff(c_404,plain,(
    ! [A_86,B_87] :
      ( r2_hidden(A_86,B_87)
      | v1_xboole_0(B_87)
      | ~ m1_subset_1(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_409,plain,(
    ! [A_86] :
      ( ~ m1_subset_1(A_86,'#skF_3')
      | v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(A_86,k1_relset_1('#skF_3','#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_404,c_28])).

tff(c_475,plain,(
    ! [A_103] :
      ( ~ m1_subset_1(A_103,'#skF_3')
      | ~ m1_subset_1(A_103,k1_relset_1('#skF_3','#skF_2','#skF_4')) ) ),
    inference(splitLeft,[status(thm)],[c_409])).

tff(c_480,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_475])).

tff(c_532,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_480])).

tff(c_673,plain,(
    ! [D_131,B_132,C_133,A_134] :
      ( m1_subset_1(D_131,k1_zfmisc_1(k2_zfmisc_1(B_132,C_133)))
      | ~ r1_tarski(k1_relat_1(D_131),B_132)
      | ~ m1_subset_1(D_131,k1_zfmisc_1(k2_zfmisc_1(A_134,C_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_688,plain,(
    ! [B_135] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_135,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_135) ) ),
    inference(resolution,[status(thm)],[c_32,c_673])).

tff(c_18,plain,(
    ! [C_15,A_12,B_13] :
      ( v1_xboole_0(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_705,plain,(
    ! [B_135] :
      ( v1_xboole_0('#skF_4')
      | ~ v1_xboole_0(B_135)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_135) ) ),
    inference(resolution,[status(thm)],[c_688,c_18])).

tff(c_708,plain,(
    ! [B_136] :
      ( ~ v1_xboole_0(B_136)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_136) ) ),
    inference(splitLeft,[status(thm)],[c_705])).

tff(c_713,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_708])).

tff(c_551,plain,(
    ! [A_115,B_116,C_117] :
      ( m1_subset_1(k1_relset_1(A_115,B_116,C_117),k1_zfmisc_1(A_115))
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_568,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_551])).

tff(c_574,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_568])).

tff(c_578,plain,(
    ! [A_118] :
      ( m1_subset_1(A_118,'#skF_3')
      | ~ r2_hidden(A_118,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_574,c_14])).

tff(c_583,plain,(
    ! [A_6] :
      ( m1_subset_1(A_6,'#skF_3')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_6,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_12,c_578])).

tff(c_750,plain,(
    ! [A_141] :
      ( m1_subset_1(A_141,'#skF_3')
      | ~ m1_subset_1(A_141,k1_relat_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_713,c_583])).

tff(c_754,plain,(
    m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_750])).

tff(c_758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_532,c_754])).

tff(c_759,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_705])).

tff(c_45,plain,(
    ! [A_44] :
      ( k2_relat_1(A_44) = k1_xboole_0
      | ~ v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_41,c_2])).

tff(c_766,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_759,c_45])).

tff(c_775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_496,c_766])).

tff(c_776,plain,(
    v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_409])).

tff(c_784,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_776,c_2])).

tff(c_837,plain,(
    ! [A_149,B_150,C_151] :
      ( k1_relset_1(A_149,B_150,C_151) = k1_relat_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_843,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_837])).

tff(c_850,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_784,c_843])).

tff(c_990,plain,(
    ! [D_169,B_170,C_171,A_172] :
      ( m1_subset_1(D_169,k1_zfmisc_1(k2_zfmisc_1(B_170,C_171)))
      | ~ r1_tarski(k1_relat_1(D_169),B_170)
      | ~ m1_subset_1(D_169,k1_zfmisc_1(k2_zfmisc_1(A_172,C_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_997,plain,(
    ! [B_170] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_170,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_170) ) ),
    inference(resolution,[status(thm)],[c_32,c_990])).

tff(c_1006,plain,(
    ! [B_173] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_173,'#skF_2')))
      | ~ r1_tarski(k1_xboole_0,B_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_997])).

tff(c_1025,plain,(
    ! [B_173] :
      ( v1_xboole_0('#skF_4')
      | ~ v1_xboole_0(B_173)
      | ~ r1_tarski(k1_xboole_0,B_173) ) ),
    inference(resolution,[status(thm)],[c_1006,c_18])).

tff(c_1028,plain,(
    ! [B_174] :
      ( ~ v1_xboole_0(B_174)
      | ~ r1_tarski(k1_xboole_0,B_174) ) ),
    inference(splitLeft,[status(thm)],[c_1025])).

tff(c_1032,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_1028])).

tff(c_1036,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_1032])).

tff(c_1037,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1025])).

tff(c_1044,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1037,c_45])).

tff(c_1053,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_888,c_1044])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.46  
% 2.97/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.46  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.97/1.46  
% 2.97/1.46  %Foreground sorts:
% 2.97/1.46  
% 2.97/1.46  
% 2.97/1.46  %Background operators:
% 2.97/1.46  
% 2.97/1.46  
% 2.97/1.46  %Foreground operators:
% 2.97/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.97/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.97/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.97/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.97/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.97/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.97/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.97/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.97/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.97/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.97/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.97/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.46  
% 3.13/1.48  tff(f_100, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 3.13/1.48  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.13/1.48  tff(f_38, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.13/1.48  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 3.13/1.48  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.13/1.48  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.13/1.48  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.13/1.48  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.13/1.48  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.13/1.48  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.13/1.48  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 3.13/1.48  tff(f_61, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 3.13/1.48  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.13/1.48  tff(c_873, plain, (![A_155, B_156, C_157]: (k2_relset_1(A_155, B_156, C_157)=k2_relat_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.13/1.48  tff(c_886, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_873])).
% 3.13/1.48  tff(c_30, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.13/1.48  tff(c_888, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_886, c_30])).
% 3.13/1.48  tff(c_10, plain, (![A_4]: (m1_subset_1('#skF_1'(A_4), A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.13/1.48  tff(c_16, plain, (![A_11]: (v1_xboole_0(k2_relat_1(A_11)) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.13/1.48  tff(c_41, plain, (![A_44]: (v1_xboole_0(k2_relat_1(A_44)) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.13/1.48  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.13/1.48  tff(c_46, plain, (![A_45]: (k2_relat_1(A_45)=k1_xboole_0 | ~v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_41, c_2])).
% 3.13/1.48  tff(c_52, plain, (![A_47]: (k2_relat_1(k2_relat_1(A_47))=k1_xboole_0 | ~v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_16, c_46])).
% 3.13/1.48  tff(c_61, plain, (![A_47]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k2_relat_1(A_47)) | ~v1_xboole_0(A_47))), inference(superposition, [status(thm), theory('equality')], [c_52, c_16])).
% 3.13/1.48  tff(c_71, plain, (![A_48]: (~v1_xboole_0(k2_relat_1(A_48)) | ~v1_xboole_0(A_48))), inference(splitLeft, [status(thm)], [c_61])).
% 3.13/1.48  tff(c_78, plain, (![A_11]: (~v1_xboole_0(A_11))), inference(resolution, [status(thm)], [c_16, c_71])).
% 3.13/1.48  tff(c_12, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.13/1.48  tff(c_88, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | ~m1_subset_1(A_6, B_7))), inference(negUnitSimplification, [status(thm)], [c_78, c_12])).
% 3.13/1.48  tff(c_102, plain, (![A_55, C_56, B_57]: (m1_subset_1(A_55, C_56) | ~m1_subset_1(B_57, k1_zfmisc_1(C_56)) | ~r2_hidden(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.13/1.48  tff(c_111, plain, (![A_59, C_60]: (m1_subset_1(A_59, C_60) | ~r2_hidden(A_59, '#skF_1'(k1_zfmisc_1(C_60))))), inference(resolution, [status(thm)], [c_10, c_102])).
% 3.13/1.48  tff(c_117, plain, (![A_61, C_62]: (m1_subset_1(A_61, C_62) | ~m1_subset_1(A_61, '#skF_1'(k1_zfmisc_1(C_62))))), inference(resolution, [status(thm)], [c_88, c_111])).
% 3.13/1.48  tff(c_138, plain, (![C_66]: (m1_subset_1('#skF_1'('#skF_1'(k1_zfmisc_1(C_66))), C_66))), inference(resolution, [status(thm)], [c_10, c_117])).
% 3.13/1.48  tff(c_14, plain, (![A_8, C_10, B_9]: (m1_subset_1(A_8, C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.13/1.48  tff(c_178, plain, (![A_68, C_69]: (m1_subset_1(A_68, C_69) | ~r2_hidden(A_68, '#skF_1'('#skF_1'(k1_zfmisc_1(k1_zfmisc_1(C_69))))))), inference(resolution, [status(thm)], [c_138, c_14])).
% 3.13/1.48  tff(c_204, plain, (![A_71, C_72]: (m1_subset_1(A_71, C_72) | ~m1_subset_1(A_71, '#skF_1'('#skF_1'(k1_zfmisc_1(k1_zfmisc_1(C_72))))))), inference(resolution, [status(thm)], [c_88, c_178])).
% 3.13/1.48  tff(c_224, plain, (![C_72]: (m1_subset_1('#skF_1'('#skF_1'('#skF_1'(k1_zfmisc_1(k1_zfmisc_1(C_72))))), C_72))), inference(resolution, [status(thm)], [c_10, c_204])).
% 3.13/1.48  tff(c_250, plain, (![A_74, B_75, C_76]: (k1_relset_1(A_74, B_75, C_76)=k1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.13/1.48  tff(c_278, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_250])).
% 3.13/1.48  tff(c_89, plain, (![A_52, B_53]: (r2_hidden(A_52, B_53) | ~m1_subset_1(A_52, B_53))), inference(negUnitSimplification, [status(thm)], [c_78, c_12])).
% 3.13/1.48  tff(c_28, plain, (![D_40]: (~r2_hidden(D_40, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_40, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.13/1.48  tff(c_94, plain, (![A_52]: (~m1_subset_1(A_52, '#skF_3') | ~m1_subset_1(A_52, k1_relset_1('#skF_3', '#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_89, c_28])).
% 3.13/1.48  tff(c_294, plain, (![A_78]: (~m1_subset_1(A_78, '#skF_3') | ~m1_subset_1(A_78, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_278, c_94])).
% 3.13/1.48  tff(c_315, plain, (~m1_subset_1('#skF_1'('#skF_1'('#skF_1'(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4')))))), '#skF_3')), inference(resolution, [status(thm)], [c_224, c_294])).
% 3.13/1.48  tff(c_320, plain, (![A_79, B_80, C_81]: (m1_subset_1(k1_relset_1(A_79, B_80, C_81), k1_zfmisc_1(A_79)) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.13/1.48  tff(c_333, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_278, c_320])).
% 3.13/1.48  tff(c_338, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_333])).
% 3.13/1.48  tff(c_342, plain, (![A_82]: (m1_subset_1(A_82, '#skF_3') | ~r2_hidden(A_82, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_338, c_14])).
% 3.13/1.48  tff(c_348, plain, (![A_83]: (m1_subset_1(A_83, '#skF_3') | ~m1_subset_1(A_83, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_88, c_342])).
% 3.13/1.48  tff(c_352, plain, (m1_subset_1('#skF_1'('#skF_1'('#skF_1'(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4')))))), '#skF_3')), inference(resolution, [status(thm)], [c_224, c_348])).
% 3.13/1.48  tff(c_372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_315, c_352])).
% 3.13/1.48  tff(c_373, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_61])).
% 3.13/1.48  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.13/1.48  tff(c_481, plain, (![A_104, B_105, C_106]: (k2_relset_1(A_104, B_105, C_106)=k2_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.13/1.48  tff(c_494, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_481])).
% 3.13/1.48  tff(c_496, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_494, c_30])).
% 3.13/1.48  tff(c_511, plain, (![A_109, B_110, C_111]: (k1_relset_1(A_109, B_110, C_111)=k1_relat_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.13/1.48  tff(c_523, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_511])).
% 3.13/1.48  tff(c_404, plain, (![A_86, B_87]: (r2_hidden(A_86, B_87) | v1_xboole_0(B_87) | ~m1_subset_1(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.13/1.48  tff(c_409, plain, (![A_86]: (~m1_subset_1(A_86, '#skF_3') | v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(A_86, k1_relset_1('#skF_3', '#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_404, c_28])).
% 3.13/1.48  tff(c_475, plain, (![A_103]: (~m1_subset_1(A_103, '#skF_3') | ~m1_subset_1(A_103, k1_relset_1('#skF_3', '#skF_2', '#skF_4')))), inference(splitLeft, [status(thm)], [c_409])).
% 3.13/1.48  tff(c_480, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_10, c_475])).
% 3.13/1.48  tff(c_532, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_523, c_480])).
% 3.13/1.48  tff(c_673, plain, (![D_131, B_132, C_133, A_134]: (m1_subset_1(D_131, k1_zfmisc_1(k2_zfmisc_1(B_132, C_133))) | ~r1_tarski(k1_relat_1(D_131), B_132) | ~m1_subset_1(D_131, k1_zfmisc_1(k2_zfmisc_1(A_134, C_133))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.13/1.48  tff(c_688, plain, (![B_135]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_135, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_135))), inference(resolution, [status(thm)], [c_32, c_673])).
% 3.13/1.48  tff(c_18, plain, (![C_15, A_12, B_13]: (v1_xboole_0(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.13/1.48  tff(c_705, plain, (![B_135]: (v1_xboole_0('#skF_4') | ~v1_xboole_0(B_135) | ~r1_tarski(k1_relat_1('#skF_4'), B_135))), inference(resolution, [status(thm)], [c_688, c_18])).
% 3.13/1.48  tff(c_708, plain, (![B_136]: (~v1_xboole_0(B_136) | ~r1_tarski(k1_relat_1('#skF_4'), B_136))), inference(splitLeft, [status(thm)], [c_705])).
% 3.13/1.48  tff(c_713, plain, (~v1_xboole_0(k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_708])).
% 3.13/1.48  tff(c_551, plain, (![A_115, B_116, C_117]: (m1_subset_1(k1_relset_1(A_115, B_116, C_117), k1_zfmisc_1(A_115)) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.13/1.48  tff(c_568, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_523, c_551])).
% 3.13/1.48  tff(c_574, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_568])).
% 3.13/1.48  tff(c_578, plain, (![A_118]: (m1_subset_1(A_118, '#skF_3') | ~r2_hidden(A_118, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_574, c_14])).
% 3.13/1.48  tff(c_583, plain, (![A_6]: (m1_subset_1(A_6, '#skF_3') | v1_xboole_0(k1_relat_1('#skF_4')) | ~m1_subset_1(A_6, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_12, c_578])).
% 3.13/1.48  tff(c_750, plain, (![A_141]: (m1_subset_1(A_141, '#skF_3') | ~m1_subset_1(A_141, k1_relat_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_713, c_583])).
% 3.13/1.48  tff(c_754, plain, (m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_10, c_750])).
% 3.13/1.48  tff(c_758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_532, c_754])).
% 3.13/1.48  tff(c_759, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_705])).
% 3.13/1.48  tff(c_45, plain, (![A_44]: (k2_relat_1(A_44)=k1_xboole_0 | ~v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_41, c_2])).
% 3.13/1.48  tff(c_766, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_759, c_45])).
% 3.13/1.48  tff(c_775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_496, c_766])).
% 3.13/1.48  tff(c_776, plain, (v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_409])).
% 3.13/1.48  tff(c_784, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_776, c_2])).
% 3.13/1.48  tff(c_837, plain, (![A_149, B_150, C_151]: (k1_relset_1(A_149, B_150, C_151)=k1_relat_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.13/1.48  tff(c_843, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_837])).
% 3.13/1.48  tff(c_850, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_784, c_843])).
% 3.13/1.48  tff(c_990, plain, (![D_169, B_170, C_171, A_172]: (m1_subset_1(D_169, k1_zfmisc_1(k2_zfmisc_1(B_170, C_171))) | ~r1_tarski(k1_relat_1(D_169), B_170) | ~m1_subset_1(D_169, k1_zfmisc_1(k2_zfmisc_1(A_172, C_171))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.13/1.48  tff(c_997, plain, (![B_170]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_170, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_170))), inference(resolution, [status(thm)], [c_32, c_990])).
% 3.13/1.48  tff(c_1006, plain, (![B_173]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_173, '#skF_2'))) | ~r1_tarski(k1_xboole_0, B_173))), inference(demodulation, [status(thm), theory('equality')], [c_850, c_997])).
% 3.13/1.48  tff(c_1025, plain, (![B_173]: (v1_xboole_0('#skF_4') | ~v1_xboole_0(B_173) | ~r1_tarski(k1_xboole_0, B_173))), inference(resolution, [status(thm)], [c_1006, c_18])).
% 3.13/1.48  tff(c_1028, plain, (![B_174]: (~v1_xboole_0(B_174) | ~r1_tarski(k1_xboole_0, B_174))), inference(splitLeft, [status(thm)], [c_1025])).
% 3.13/1.48  tff(c_1032, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1028])).
% 3.13/1.48  tff(c_1036, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_373, c_1032])).
% 3.13/1.48  tff(c_1037, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1025])).
% 3.13/1.48  tff(c_1044, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1037, c_45])).
% 3.13/1.48  tff(c_1053, plain, $false, inference(negUnitSimplification, [status(thm)], [c_888, c_1044])).
% 3.13/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.48  
% 3.13/1.48  Inference rules
% 3.13/1.48  ----------------------
% 3.13/1.48  #Ref     : 0
% 3.13/1.48  #Sup     : 227
% 3.13/1.48  #Fact    : 0
% 3.13/1.48  #Define  : 0
% 3.13/1.48  #Split   : 4
% 3.13/1.48  #Chain   : 0
% 3.13/1.48  #Close   : 0
% 3.13/1.48  
% 3.13/1.48  Ordering : KBO
% 3.13/1.48  
% 3.13/1.48  Simplification rules
% 3.13/1.48  ----------------------
% 3.13/1.48  #Subsume      : 20
% 3.13/1.48  #Demod        : 58
% 3.13/1.48  #Tautology    : 77
% 3.13/1.48  #SimpNegUnit  : 8
% 3.13/1.48  #BackRed      : 12
% 3.13/1.48  
% 3.13/1.48  #Partial instantiations: 0
% 3.13/1.48  #Strategies tried      : 1
% 3.13/1.48  
% 3.13/1.48  Timing (in seconds)
% 3.13/1.48  ----------------------
% 3.13/1.48  Preprocessing        : 0.31
% 3.13/1.48  Parsing              : 0.17
% 3.13/1.48  CNF conversion       : 0.02
% 3.13/1.48  Main loop            : 0.37
% 3.13/1.48  Inferencing          : 0.14
% 3.13/1.48  Reduction            : 0.11
% 3.13/1.48  Demodulation         : 0.08
% 3.13/1.48  BG Simplification    : 0.02
% 3.13/1.48  Subsumption          : 0.07
% 3.13/1.48  Abstraction          : 0.02
% 3.13/1.48  MUC search           : 0.00
% 3.13/1.48  Cooper               : 0.00
% 3.13/1.48  Total                : 0.73
% 3.13/1.48  Index Insertion      : 0.00
% 3.13/1.48  Index Deletion       : 0.00
% 3.13/1.48  Index Matching       : 0.00
% 3.13/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
