%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:22 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 279 expanded)
%              Number of leaves         :   38 ( 107 expanded)
%              Depth                    :   13
%              Number of atoms          :  196 ( 542 expanded)
%              Number of equality atoms :   29 (  74 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
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

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2480,plain,(
    ! [A_329,B_330,C_331] :
      ( k2_relset_1(A_329,B_330,C_331) = k2_relat_1(C_331)
      | ~ m1_subset_1(C_331,k1_zfmisc_1(k2_zfmisc_1(A_329,B_330))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2507,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_2480])).

tff(c_42,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2509,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2507,c_42])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_190,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_203,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_190])).

tff(c_249,plain,(
    ! [C_91,A_92,B_93] :
      ( v4_relat_1(C_91,A_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_262,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_249])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [A_20] :
      ( v1_xboole_0(k2_relat_1(A_20))
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_62,plain,(
    ! [A_54] :
      ( v1_xboole_0(k2_relat_1(A_54))
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ! [A_55] :
      ( k2_relat_1(A_55) = k1_xboole_0
      | ~ v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_62,c_6])).

tff(c_93,plain,(
    ! [A_61] :
      ( k2_relat_1(k2_relat_1(A_61)) = k1_xboole_0
      | ~ v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_26,c_67])).

tff(c_102,plain,(
    ! [A_61] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k2_relat_1(A_61))
      | ~ v1_xboole_0(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_26])).

tff(c_169,plain,(
    ! [A_72] :
      ( ~ v1_xboole_0(k2_relat_1(A_72))
      | ~ v1_xboole_0(A_72) ) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_179,plain,(
    ! [A_20] : ~ v1_xboole_0(A_20) ),
    inference(resolution,[status(thm)],[c_26,c_169])).

tff(c_181,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_4])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_304,plain,(
    ! [A_104,C_105,B_106] :
      ( m1_subset_1(A_104,C_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(C_105))
      | ~ r2_hidden(A_104,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_503,plain,(
    ! [A_135,B_136,A_137] :
      ( m1_subset_1(A_135,B_136)
      | ~ r2_hidden(A_135,A_137)
      | ~ r1_tarski(A_137,B_136) ) ),
    inference(resolution,[status(thm)],[c_16,c_304])).

tff(c_507,plain,(
    ! [A_138,B_139] :
      ( m1_subset_1('#skF_1'(A_138),B_139)
      | ~ r1_tarski(A_138,B_139) ) ),
    inference(resolution,[status(thm)],[c_181,c_503])).

tff(c_344,plain,(
    ! [A_110,B_111,C_112] :
      ( k1_relset_1(A_110,B_111,C_112) = k1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_362,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_344])).

tff(c_184,plain,(
    ! [A_74] : r2_hidden('#skF_1'(A_74),A_74) ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_4])).

tff(c_40,plain,(
    ! [D_48] :
      ( ~ r2_hidden(D_48,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_48,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_189,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_184,c_40])).

tff(c_380,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_189])).

tff(c_543,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_507,c_380])).

tff(c_552,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_543])).

tff(c_556,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_262,c_552])).

tff(c_557,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_10,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_49,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_111,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(A_62,B_63)
      | ~ m1_subset_1(A_62,k1_zfmisc_1(B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_119,plain,(
    ! [A_9] : r1_tarski(A_9,A_9) ),
    inference(resolution,[status(thm)],[c_49,c_111])).

tff(c_77,plain,(
    ! [A_57,B_58] :
      ( v1_xboole_0(k2_zfmisc_1(A_57,B_58))
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [A_57,B_58] :
      ( k2_zfmisc_1(A_57,B_58) = k1_xboole_0
      | ~ v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_77,c_6])).

tff(c_1718,plain,(
    ! [B_58] : k2_zfmisc_1(k1_xboole_0,B_58) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_557,c_85])).

tff(c_1005,plain,(
    ! [A_199,B_200,C_201] :
      ( k2_relset_1(A_199,B_200,C_201) = k2_relat_1(C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1031,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1005])).

tff(c_1033,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1031,c_42])).

tff(c_608,plain,(
    ! [C_141,A_142,B_143] :
      ( v1_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_625,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_608])).

tff(c_663,plain,(
    ! [C_152,A_153,B_154] :
      ( v4_relat_1(C_152,A_153)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_682,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_663])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_xboole_0(k2_zfmisc_1(A_6,B_7))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1052,plain,(
    ! [D_203,B_204,C_205,A_206] :
      ( m1_subset_1(D_203,k1_zfmisc_1(k2_zfmisc_1(B_204,C_205)))
      | ~ r1_tarski(k1_relat_1(D_203),B_204)
      | ~ m1_subset_1(D_203,k1_zfmisc_1(k2_zfmisc_1(A_206,C_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1250,plain,(
    ! [B_224] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_224,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_224) ) ),
    inference(resolution,[status(thm)],[c_44,c_1052])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1361,plain,(
    ! [B_228] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_228,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_228) ) ),
    inference(resolution,[status(thm)],[c_1250,c_14])).

tff(c_1380,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_119,c_1361])).

tff(c_691,plain,(
    ! [C_157,B_158,A_159] :
      ( ~ v1_xboole_0(C_157)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(C_157))
      | ~ r2_hidden(A_159,B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1074,plain,(
    ! [B_207,A_208,A_209] :
      ( ~ v1_xboole_0(B_207)
      | ~ r2_hidden(A_208,A_209)
      | ~ r1_tarski(A_209,B_207) ) ),
    inference(resolution,[status(thm)],[c_16,c_691])).

tff(c_1077,plain,(
    ! [B_207,A_1] :
      ( ~ v1_xboole_0(B_207)
      | ~ r1_tarski(A_1,B_207)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_1074])).

tff(c_1395,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1380,c_1077])).

tff(c_1407,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1395])).

tff(c_1430,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_1407])).

tff(c_825,plain,(
    ! [A_180,C_181,B_182] :
      ( m1_subset_1(A_180,C_181)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(C_181))
      | ~ r2_hidden(A_180,B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1208,plain,(
    ! [A_220,B_221,A_222] :
      ( m1_subset_1(A_220,B_221)
      | ~ r2_hidden(A_220,A_222)
      | ~ r1_tarski(A_222,B_221) ) ),
    inference(resolution,[status(thm)],[c_16,c_825])).

tff(c_1587,plain,(
    ! [A_243,B_244] :
      ( m1_subset_1('#skF_1'(A_243),B_244)
      | ~ r1_tarski(A_243,B_244)
      | v1_xboole_0(A_243) ) ),
    inference(resolution,[status(thm)],[c_4,c_1208])).

tff(c_933,plain,(
    ! [A_188,B_189,C_190] :
      ( k1_relset_1(A_188,B_189,C_190) = k1_relat_1(C_190)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_959,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_933])).

tff(c_141,plain,(
    ! [D_69] :
      ( ~ r2_hidden(D_69,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_69,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_146,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3')
    | v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_141])).

tff(c_558,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_962,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_959,c_558])).

tff(c_1601,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1587,c_962])).

tff(c_1637,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1430,c_1601])).

tff(c_1688,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1637])).

tff(c_1692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_682,c_1688])).

tff(c_1693,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1395])).

tff(c_66,plain,(
    ! [A_54] :
      ( k2_relat_1(A_54) = k1_xboole_0
      | ~ v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_62,c_6])).

tff(c_1699,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1693,c_66])).

tff(c_1707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1033,c_1699])).

tff(c_1708,plain,(
    v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_1732,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1708,c_6])).

tff(c_2515,plain,(
    ! [A_333,B_334,C_335] :
      ( k1_relset_1(A_333,B_334,C_335) = k1_relat_1(C_335)
      | ~ m1_subset_1(C_335,k1_zfmisc_1(k2_zfmisc_1(A_333,B_334))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2535,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_2515])).

tff(c_2543,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1732,c_2535])).

tff(c_2597,plain,(
    ! [D_338,B_339,C_340,A_341] :
      ( m1_subset_1(D_338,k1_zfmisc_1(k2_zfmisc_1(B_339,C_340)))
      | ~ r1_tarski(k1_relat_1(D_338),B_339)
      | ~ m1_subset_1(D_338,k1_zfmisc_1(k2_zfmisc_1(A_341,C_340))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2611,plain,(
    ! [B_339] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_339,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_339) ) ),
    inference(resolution,[status(thm)],[c_44,c_2597])).

tff(c_2622,plain,(
    ! [B_342] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_342,'#skF_2')))
      | ~ r1_tarski(k1_xboole_0,B_342) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2543,c_2611])).

tff(c_2654,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1718,c_2622])).

tff(c_2673,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_2654])).

tff(c_20,plain,(
    ! [C_17,B_16,A_15] :
      ( ~ v1_xboole_0(C_17)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(C_17))
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2680,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_15,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2673,c_20])).

tff(c_2699,plain,(
    ! [A_343] : ~ r2_hidden(A_343,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_2680])).

tff(c_2704,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_2699])).

tff(c_2709,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2704,c_66])).

tff(c_2717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2509,c_2709])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.98/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.79  
% 4.41/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.79  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 4.41/1.79  
% 4.41/1.79  %Foreground sorts:
% 4.41/1.79  
% 4.41/1.79  
% 4.41/1.79  %Background operators:
% 4.41/1.79  
% 4.41/1.79  
% 4.41/1.79  %Foreground operators:
% 4.41/1.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.41/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.41/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.41/1.79  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.41/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.41/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.41/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.41/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.41/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.41/1.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.41/1.79  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.41/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.41/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.41/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.41/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.41/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.41/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.41/1.79  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.41/1.79  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.41/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.41/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.41/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.41/1.79  
% 4.52/1.81  tff(f_115, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 4.52/1.81  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.52/1.81  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.52/1.81  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.52/1.81  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.52/1.81  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.52/1.81  tff(f_70, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 4.52/1.81  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.52/1.81  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.52/1.81  tff(f_53, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.52/1.81  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.52/1.81  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.52/1.81  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.52/1.81  tff(f_39, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 4.52/1.81  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 4.52/1.81  tff(f_60, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.52/1.81  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.52/1.81  tff(c_2480, plain, (![A_329, B_330, C_331]: (k2_relset_1(A_329, B_330, C_331)=k2_relat_1(C_331) | ~m1_subset_1(C_331, k1_zfmisc_1(k2_zfmisc_1(A_329, B_330))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.52/1.81  tff(c_2507, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_2480])).
% 4.52/1.81  tff(c_42, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.52/1.81  tff(c_2509, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2507, c_42])).
% 4.52/1.81  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.52/1.81  tff(c_190, plain, (![C_75, A_76, B_77]: (v1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.52/1.81  tff(c_203, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_190])).
% 4.52/1.81  tff(c_249, plain, (![C_91, A_92, B_93]: (v4_relat_1(C_91, A_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.52/1.81  tff(c_262, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_249])).
% 4.52/1.81  tff(c_24, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(B_19), A_18) | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.52/1.81  tff(c_26, plain, (![A_20]: (v1_xboole_0(k2_relat_1(A_20)) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.52/1.81  tff(c_62, plain, (![A_54]: (v1_xboole_0(k2_relat_1(A_54)) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.52/1.81  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.52/1.81  tff(c_67, plain, (![A_55]: (k2_relat_1(A_55)=k1_xboole_0 | ~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_62, c_6])).
% 4.52/1.81  tff(c_93, plain, (![A_61]: (k2_relat_1(k2_relat_1(A_61))=k1_xboole_0 | ~v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_26, c_67])).
% 4.52/1.81  tff(c_102, plain, (![A_61]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k2_relat_1(A_61)) | ~v1_xboole_0(A_61))), inference(superposition, [status(thm), theory('equality')], [c_93, c_26])).
% 4.52/1.81  tff(c_169, plain, (![A_72]: (~v1_xboole_0(k2_relat_1(A_72)) | ~v1_xboole_0(A_72))), inference(splitLeft, [status(thm)], [c_102])).
% 4.52/1.81  tff(c_179, plain, (![A_20]: (~v1_xboole_0(A_20))), inference(resolution, [status(thm)], [c_26, c_169])).
% 4.52/1.81  tff(c_181, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_179, c_4])).
% 4.52/1.81  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.52/1.81  tff(c_304, plain, (![A_104, C_105, B_106]: (m1_subset_1(A_104, C_105) | ~m1_subset_1(B_106, k1_zfmisc_1(C_105)) | ~r2_hidden(A_104, B_106))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.52/1.81  tff(c_503, plain, (![A_135, B_136, A_137]: (m1_subset_1(A_135, B_136) | ~r2_hidden(A_135, A_137) | ~r1_tarski(A_137, B_136))), inference(resolution, [status(thm)], [c_16, c_304])).
% 4.52/1.81  tff(c_507, plain, (![A_138, B_139]: (m1_subset_1('#skF_1'(A_138), B_139) | ~r1_tarski(A_138, B_139))), inference(resolution, [status(thm)], [c_181, c_503])).
% 4.52/1.81  tff(c_344, plain, (![A_110, B_111, C_112]: (k1_relset_1(A_110, B_111, C_112)=k1_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.52/1.81  tff(c_362, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_344])).
% 4.52/1.81  tff(c_184, plain, (![A_74]: (r2_hidden('#skF_1'(A_74), A_74))), inference(negUnitSimplification, [status(thm)], [c_179, c_4])).
% 4.52/1.81  tff(c_40, plain, (![D_48]: (~r2_hidden(D_48, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_48, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.52/1.81  tff(c_189, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_184, c_40])).
% 4.52/1.81  tff(c_380, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_362, c_189])).
% 4.52/1.81  tff(c_543, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_507, c_380])).
% 4.52/1.81  tff(c_552, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_543])).
% 4.52/1.81  tff(c_556, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_203, c_262, c_552])).
% 4.52/1.81  tff(c_557, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_102])).
% 4.52/1.81  tff(c_10, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.52/1.81  tff(c_12, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.52/1.81  tff(c_49, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 4.52/1.81  tff(c_111, plain, (![A_62, B_63]: (r1_tarski(A_62, B_63) | ~m1_subset_1(A_62, k1_zfmisc_1(B_63)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.52/1.81  tff(c_119, plain, (![A_9]: (r1_tarski(A_9, A_9))), inference(resolution, [status(thm)], [c_49, c_111])).
% 4.52/1.81  tff(c_77, plain, (![A_57, B_58]: (v1_xboole_0(k2_zfmisc_1(A_57, B_58)) | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.52/1.81  tff(c_85, plain, (![A_57, B_58]: (k2_zfmisc_1(A_57, B_58)=k1_xboole_0 | ~v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_77, c_6])).
% 4.52/1.81  tff(c_1718, plain, (![B_58]: (k2_zfmisc_1(k1_xboole_0, B_58)=k1_xboole_0)), inference(resolution, [status(thm)], [c_557, c_85])).
% 4.52/1.81  tff(c_1005, plain, (![A_199, B_200, C_201]: (k2_relset_1(A_199, B_200, C_201)=k2_relat_1(C_201) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.52/1.81  tff(c_1031, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1005])).
% 4.52/1.81  tff(c_1033, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1031, c_42])).
% 4.52/1.81  tff(c_608, plain, (![C_141, A_142, B_143]: (v1_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.52/1.81  tff(c_625, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_608])).
% 4.52/1.81  tff(c_663, plain, (![C_152, A_153, B_154]: (v4_relat_1(C_152, A_153) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.52/1.81  tff(c_682, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_663])).
% 4.52/1.81  tff(c_8, plain, (![A_6, B_7]: (v1_xboole_0(k2_zfmisc_1(A_6, B_7)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.52/1.81  tff(c_1052, plain, (![D_203, B_204, C_205, A_206]: (m1_subset_1(D_203, k1_zfmisc_1(k2_zfmisc_1(B_204, C_205))) | ~r1_tarski(k1_relat_1(D_203), B_204) | ~m1_subset_1(D_203, k1_zfmisc_1(k2_zfmisc_1(A_206, C_205))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.52/1.81  tff(c_1250, plain, (![B_224]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_224, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_224))), inference(resolution, [status(thm)], [c_44, c_1052])).
% 4.52/1.81  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.52/1.81  tff(c_1361, plain, (![B_228]: (r1_tarski('#skF_4', k2_zfmisc_1(B_228, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_4'), B_228))), inference(resolution, [status(thm)], [c_1250, c_14])).
% 4.52/1.81  tff(c_1380, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2'))), inference(resolution, [status(thm)], [c_119, c_1361])).
% 4.52/1.81  tff(c_691, plain, (![C_157, B_158, A_159]: (~v1_xboole_0(C_157) | ~m1_subset_1(B_158, k1_zfmisc_1(C_157)) | ~r2_hidden(A_159, B_158))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.52/1.81  tff(c_1074, plain, (![B_207, A_208, A_209]: (~v1_xboole_0(B_207) | ~r2_hidden(A_208, A_209) | ~r1_tarski(A_209, B_207))), inference(resolution, [status(thm)], [c_16, c_691])).
% 4.52/1.81  tff(c_1077, plain, (![B_207, A_1]: (~v1_xboole_0(B_207) | ~r1_tarski(A_1, B_207) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_1074])).
% 4.52/1.81  tff(c_1395, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1380, c_1077])).
% 4.52/1.81  tff(c_1407, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_1395])).
% 4.52/1.81  tff(c_1430, plain, (~v1_xboole_0(k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_1407])).
% 4.52/1.81  tff(c_825, plain, (![A_180, C_181, B_182]: (m1_subset_1(A_180, C_181) | ~m1_subset_1(B_182, k1_zfmisc_1(C_181)) | ~r2_hidden(A_180, B_182))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.52/1.81  tff(c_1208, plain, (![A_220, B_221, A_222]: (m1_subset_1(A_220, B_221) | ~r2_hidden(A_220, A_222) | ~r1_tarski(A_222, B_221))), inference(resolution, [status(thm)], [c_16, c_825])).
% 4.52/1.81  tff(c_1587, plain, (![A_243, B_244]: (m1_subset_1('#skF_1'(A_243), B_244) | ~r1_tarski(A_243, B_244) | v1_xboole_0(A_243))), inference(resolution, [status(thm)], [c_4, c_1208])).
% 4.52/1.81  tff(c_933, plain, (![A_188, B_189, C_190]: (k1_relset_1(A_188, B_189, C_190)=k1_relat_1(C_190) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.52/1.81  tff(c_959, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_933])).
% 4.52/1.81  tff(c_141, plain, (![D_69]: (~r2_hidden(D_69, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_69, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.52/1.81  tff(c_146, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3') | v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_141])).
% 4.52/1.81  tff(c_558, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_146])).
% 4.52/1.81  tff(c_962, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_959, c_558])).
% 4.52/1.81  tff(c_1601, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | v1_xboole_0(k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1587, c_962])).
% 4.52/1.81  tff(c_1637, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1430, c_1601])).
% 4.52/1.81  tff(c_1688, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_1637])).
% 4.52/1.81  tff(c_1692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_625, c_682, c_1688])).
% 4.52/1.81  tff(c_1693, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1395])).
% 4.52/1.81  tff(c_66, plain, (![A_54]: (k2_relat_1(A_54)=k1_xboole_0 | ~v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_62, c_6])).
% 4.52/1.81  tff(c_1699, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1693, c_66])).
% 4.52/1.81  tff(c_1707, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1033, c_1699])).
% 4.52/1.81  tff(c_1708, plain, (v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_146])).
% 4.52/1.81  tff(c_1732, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1708, c_6])).
% 4.52/1.81  tff(c_2515, plain, (![A_333, B_334, C_335]: (k1_relset_1(A_333, B_334, C_335)=k1_relat_1(C_335) | ~m1_subset_1(C_335, k1_zfmisc_1(k2_zfmisc_1(A_333, B_334))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.52/1.81  tff(c_2535, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_2515])).
% 4.52/1.81  tff(c_2543, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1732, c_2535])).
% 4.52/1.81  tff(c_2597, plain, (![D_338, B_339, C_340, A_341]: (m1_subset_1(D_338, k1_zfmisc_1(k2_zfmisc_1(B_339, C_340))) | ~r1_tarski(k1_relat_1(D_338), B_339) | ~m1_subset_1(D_338, k1_zfmisc_1(k2_zfmisc_1(A_341, C_340))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.52/1.81  tff(c_2611, plain, (![B_339]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_339, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_339))), inference(resolution, [status(thm)], [c_44, c_2597])).
% 4.52/1.81  tff(c_2622, plain, (![B_342]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_342, '#skF_2'))) | ~r1_tarski(k1_xboole_0, B_342))), inference(demodulation, [status(thm), theory('equality')], [c_2543, c_2611])).
% 4.52/1.81  tff(c_2654, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1718, c_2622])).
% 4.52/1.81  tff(c_2673, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_2654])).
% 4.52/1.81  tff(c_20, plain, (![C_17, B_16, A_15]: (~v1_xboole_0(C_17) | ~m1_subset_1(B_16, k1_zfmisc_1(C_17)) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.52/1.81  tff(c_2680, plain, (![A_15]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_15, '#skF_4'))), inference(resolution, [status(thm)], [c_2673, c_20])).
% 4.52/1.81  tff(c_2699, plain, (![A_343]: (~r2_hidden(A_343, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_557, c_2680])).
% 4.52/1.81  tff(c_2704, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_2699])).
% 4.52/1.81  tff(c_2709, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2704, c_66])).
% 4.52/1.81  tff(c_2717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2509, c_2709])).
% 4.52/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.52/1.81  
% 4.52/1.81  Inference rules
% 4.52/1.81  ----------------------
% 4.52/1.81  #Ref     : 0
% 4.52/1.81  #Sup     : 591
% 4.52/1.81  #Fact    : 0
% 4.52/1.81  #Define  : 0
% 4.52/1.81  #Split   : 8
% 4.52/1.81  #Chain   : 0
% 4.52/1.81  #Close   : 0
% 4.52/1.81  
% 4.52/1.81  Ordering : KBO
% 4.52/1.81  
% 4.52/1.81  Simplification rules
% 4.52/1.81  ----------------------
% 4.52/1.81  #Subsume      : 74
% 4.52/1.81  #Demod        : 253
% 4.52/1.81  #Tautology    : 201
% 4.52/1.81  #SimpNegUnit  : 15
% 4.52/1.81  #BackRed      : 19
% 4.52/1.81  
% 4.52/1.81  #Partial instantiations: 0
% 4.52/1.81  #Strategies tried      : 1
% 4.52/1.81  
% 4.52/1.81  Timing (in seconds)
% 4.52/1.81  ----------------------
% 4.52/1.82  Preprocessing        : 0.34
% 4.52/1.82  Parsing              : 0.19
% 4.52/1.82  CNF conversion       : 0.03
% 4.52/1.82  Main loop            : 0.64
% 4.52/1.82  Inferencing          : 0.24
% 4.52/1.82  Reduction            : 0.20
% 4.52/1.82  Demodulation         : 0.13
% 4.52/1.82  BG Simplification    : 0.03
% 4.52/1.82  Subsumption          : 0.11
% 4.52/1.82  Abstraction          : 0.03
% 4.52/1.82  MUC search           : 0.00
% 4.52/1.82  Cooper               : 0.00
% 4.52/1.82  Total                : 1.04
% 4.52/1.82  Index Insertion      : 0.00
% 4.52/1.82  Index Deletion       : 0.00
% 4.52/1.82  Index Matching       : 0.00
% 4.52/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
