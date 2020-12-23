%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:23 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 352 expanded)
%              Number of leaves         :   32 ( 127 expanded)
%              Depth                    :   13
%              Number of atoms          :  160 ( 788 expanded)
%              Number of equality atoms :   33 ( 172 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(c_28,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_89,plain,(
    ! [C_56,A_57,B_58] :
      ( v4_relat_1(C_56,A_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_98,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_89])).

tff(c_46,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_55,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_46])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_234,plain,(
    ! [A_96,B_97,C_98] :
      ( k1_relset_1(A_96,B_97,C_98) = k1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_248,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_234])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_122,plain,(
    ! [A_65,C_66,B_67] :
      ( m1_subset_1(A_65,C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_130,plain,(
    ! [A_69,B_70,A_71] :
      ( m1_subset_1(A_69,B_70)
      | ~ r2_hidden(A_69,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_122])).

tff(c_149,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1('#skF_1'(A_75),B_76)
      | ~ r1_tarski(A_75,B_76)
      | k1_xboole_0 = A_75 ) ),
    inference(resolution,[status(thm)],[c_2,c_130])).

tff(c_56,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,k1_relset_1('#skF_4','#skF_3','#skF_5'))
      | ~ m1_subset_1(D_45,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_61,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_4','#skF_3','#skF_5')),'#skF_4')
    | k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_56])).

tff(c_110,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_4','#skF_3','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_178,plain,
    ( ~ r1_tarski(k1_relset_1('#skF_4','#skF_3','#skF_5'),'#skF_4')
    | k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_149,c_110])).

tff(c_183,plain,(
    ~ r1_tarski(k1_relset_1('#skF_4','#skF_3','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_249,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_183])).

tff(c_258,plain,
    ( ~ v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_249])).

tff(c_262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_98,c_258])).

tff(c_263,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_264,plain,(
    r1_tarski(k1_relset_1('#skF_4','#skF_3','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_276,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_264])).

tff(c_134,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_143,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_134])).

tff(c_144,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_28])).

tff(c_277,plain,(
    ! [A_99,B_100,C_101] :
      ( k1_relset_1(A_99,B_100,C_101) = k1_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_288,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_277])).

tff(c_292,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_288])).

tff(c_387,plain,(
    ! [A_119,B_120] :
      ( r2_hidden('#skF_2'(A_119,B_120),k1_relat_1(B_120))
      | ~ r2_hidden(A_119,k2_relat_1(B_120))
      | ~ v1_relat_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_392,plain,(
    ! [A_119] :
      ( r2_hidden('#skF_2'(A_119,'#skF_5'),k1_xboole_0)
      | ~ r2_hidden(A_119,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_387])).

tff(c_396,plain,(
    ! [A_121] :
      ( r2_hidden('#skF_2'(A_121,'#skF_5'),k1_xboole_0)
      | ~ r2_hidden(A_121,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_392])).

tff(c_127,plain,(
    ! [A_65,B_4,A_3] :
      ( m1_subset_1(A_65,B_4)
      | ~ r2_hidden(A_65,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_122])).

tff(c_412,plain,(
    ! [A_123,B_124] :
      ( m1_subset_1('#skF_2'(A_123,'#skF_5'),B_124)
      | ~ r1_tarski(k1_xboole_0,B_124)
      | ~ r2_hidden(A_123,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_396,c_127])).

tff(c_415,plain,(
    ! [B_124] :
      ( m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')),'#skF_5'),B_124)
      | ~ r1_tarski(k1_xboole_0,B_124)
      | k2_relat_1('#skF_5') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_412])).

tff(c_419,plain,(
    ! [B_125] :
      ( m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')),'#skF_5'),B_125)
      | ~ r1_tarski(k1_xboole_0,B_125) ) ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_415])).

tff(c_26,plain,(
    ! [D_36] :
      ( ~ r2_hidden(D_36,k1_relset_1('#skF_4','#skF_3','#skF_5'))
      | ~ m1_subset_1(D_36,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_266,plain,(
    ! [D_36] :
      ( ~ r2_hidden(D_36,k1_xboole_0)
      | ~ m1_subset_1(D_36,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_26])).

tff(c_404,plain,(
    ! [A_122] :
      ( ~ m1_subset_1('#skF_2'(A_122,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_122,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_396,c_266])).

tff(c_408,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')),'#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_404])).

tff(c_411,plain,(
    ~ m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')),'#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_408])).

tff(c_422,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_419,c_411])).

tff(c_453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_422])).

tff(c_454,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_517,plain,(
    ! [A_139,B_140,C_141] :
      ( k1_relset_1(A_139,B_140,C_141) = k1_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_528,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_517])).

tff(c_532,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_528])).

tff(c_539,plain,(
    ! [A_8] :
      ( r1_tarski(k1_xboole_0,A_8)
      | ~ v4_relat_1('#skF_5',A_8)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_12])).

tff(c_548,plain,(
    ! [A_143] :
      ( r1_tarski(k1_xboole_0,A_143)
      | ~ v4_relat_1('#skF_5',A_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_539])).

tff(c_556,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_548])).

tff(c_646,plain,(
    ! [A_165,B_166,C_167] :
      ( k2_relset_1(A_165,B_166,C_167) = k2_relat_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_660,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_646])).

tff(c_661,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_660,c_28])).

tff(c_565,plain,(
    ! [A_147,B_148] :
      ( r2_hidden('#skF_2'(A_147,B_148),k1_relat_1(B_148))
      | ~ r2_hidden(A_147,k2_relat_1(B_148))
      | ~ v1_relat_1(B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_570,plain,(
    ! [A_147] :
      ( r2_hidden('#skF_2'(A_147,'#skF_5'),k1_xboole_0)
      | ~ r2_hidden(A_147,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_565])).

tff(c_574,plain,(
    ! [A_149] :
      ( r2_hidden('#skF_2'(A_149,'#skF_5'),k1_xboole_0)
      | ~ r2_hidden(A_149,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_570])).

tff(c_480,plain,(
    ! [A_130,C_131,B_132] :
      ( m1_subset_1(A_130,C_131)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(C_131))
      | ~ r2_hidden(A_130,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_485,plain,(
    ! [A_130,B_4,A_3] :
      ( m1_subset_1(A_130,B_4)
      | ~ r2_hidden(A_130,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_480])).

tff(c_682,plain,(
    ! [A_171,B_172] :
      ( m1_subset_1('#skF_2'(A_171,'#skF_5'),B_172)
      | ~ r1_tarski(k1_xboole_0,B_172)
      | ~ r2_hidden(A_171,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_574,c_485])).

tff(c_685,plain,(
    ! [B_172] :
      ( m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')),'#skF_5'),B_172)
      | ~ r1_tarski(k1_xboole_0,B_172)
      | k2_relat_1('#skF_5') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_682])).

tff(c_689,plain,(
    ! [B_173] :
      ( m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')),'#skF_5'),B_173)
      | ~ r1_tarski(k1_xboole_0,B_173) ) ),
    inference(negUnitSimplification,[status(thm)],[c_661,c_685])).

tff(c_456,plain,(
    ! [D_36] :
      ( ~ r2_hidden(D_36,k1_xboole_0)
      | ~ m1_subset_1(D_36,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_26])).

tff(c_582,plain,(
    ! [A_150] :
      ( ~ m1_subset_1('#skF_2'(A_150,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_150,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_574,c_456])).

tff(c_587,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')),'#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_582])).

tff(c_604,plain,(
    ~ m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')),'#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_587])).

tff(c_696,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_689,c_604])).

tff(c_724,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_696])).

tff(c_725,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_587])).

tff(c_744,plain,(
    ! [A_175,B_176,C_177] :
      ( k2_relset_1(A_175,B_176,C_177) = k2_relat_1(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_755,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_744])).

tff(c_759,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_725,c_755])).

tff(c_761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_759])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:30:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.45  
% 2.86/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.45  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.86/1.45  
% 2.86/1.45  %Foreground sorts:
% 2.86/1.45  
% 2.86/1.45  
% 2.86/1.45  %Background operators:
% 2.86/1.45  
% 2.86/1.45  
% 2.86/1.45  %Foreground operators:
% 2.86/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.86/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.86/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.86/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.86/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.86/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.86/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.86/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.86/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.86/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.86/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.86/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.86/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.86/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.86/1.45  
% 2.86/1.47  tff(f_97, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 2.86/1.47  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.86/1.47  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.86/1.47  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.86/1.47  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.86/1.47  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.86/1.47  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.86/1.47  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.86/1.47  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.86/1.47  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 2.86/1.47  tff(c_28, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.86/1.47  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.86/1.47  tff(c_89, plain, (![C_56, A_57, B_58]: (v4_relat_1(C_56, A_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.86/1.47  tff(c_98, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_89])).
% 2.86/1.47  tff(c_46, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.86/1.47  tff(c_55, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_46])).
% 2.86/1.47  tff(c_12, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(B_9), A_8) | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.86/1.47  tff(c_234, plain, (![A_96, B_97, C_98]: (k1_relset_1(A_96, B_97, C_98)=k1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.86/1.47  tff(c_248, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_234])).
% 2.86/1.47  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.86/1.47  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.86/1.47  tff(c_122, plain, (![A_65, C_66, B_67]: (m1_subset_1(A_65, C_66) | ~m1_subset_1(B_67, k1_zfmisc_1(C_66)) | ~r2_hidden(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.86/1.47  tff(c_130, plain, (![A_69, B_70, A_71]: (m1_subset_1(A_69, B_70) | ~r2_hidden(A_69, A_71) | ~r1_tarski(A_71, B_70))), inference(resolution, [status(thm)], [c_6, c_122])).
% 2.86/1.47  tff(c_149, plain, (![A_75, B_76]: (m1_subset_1('#skF_1'(A_75), B_76) | ~r1_tarski(A_75, B_76) | k1_xboole_0=A_75)), inference(resolution, [status(thm)], [c_2, c_130])).
% 2.86/1.47  tff(c_56, plain, (![D_45]: (~r2_hidden(D_45, k1_relset_1('#skF_4', '#skF_3', '#skF_5')) | ~m1_subset_1(D_45, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.86/1.47  tff(c_61, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_4', '#skF_3', '#skF_5')), '#skF_4') | k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_56])).
% 2.86/1.47  tff(c_110, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_4', '#skF_3', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_61])).
% 2.86/1.47  tff(c_178, plain, (~r1_tarski(k1_relset_1('#skF_4', '#skF_3', '#skF_5'), '#skF_4') | k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_149, c_110])).
% 2.86/1.47  tff(c_183, plain, (~r1_tarski(k1_relset_1('#skF_4', '#skF_3', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_178])).
% 2.86/1.47  tff(c_249, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_248, c_183])).
% 2.86/1.47  tff(c_258, plain, (~v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_249])).
% 2.86/1.47  tff(c_262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_98, c_258])).
% 2.86/1.47  tff(c_263, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_178])).
% 2.86/1.47  tff(c_264, plain, (r1_tarski(k1_relset_1('#skF_4', '#skF_3', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_178])).
% 2.86/1.47  tff(c_276, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_264])).
% 2.86/1.47  tff(c_134, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.86/1.47  tff(c_143, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_134])).
% 2.86/1.47  tff(c_144, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_143, c_28])).
% 2.86/1.47  tff(c_277, plain, (![A_99, B_100, C_101]: (k1_relset_1(A_99, B_100, C_101)=k1_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.86/1.47  tff(c_288, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_277])).
% 2.86/1.47  tff(c_292, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_263, c_288])).
% 2.86/1.47  tff(c_387, plain, (![A_119, B_120]: (r2_hidden('#skF_2'(A_119, B_120), k1_relat_1(B_120)) | ~r2_hidden(A_119, k2_relat_1(B_120)) | ~v1_relat_1(B_120))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.86/1.47  tff(c_392, plain, (![A_119]: (r2_hidden('#skF_2'(A_119, '#skF_5'), k1_xboole_0) | ~r2_hidden(A_119, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_292, c_387])).
% 2.86/1.47  tff(c_396, plain, (![A_121]: (r2_hidden('#skF_2'(A_121, '#skF_5'), k1_xboole_0) | ~r2_hidden(A_121, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_392])).
% 2.86/1.47  tff(c_127, plain, (![A_65, B_4, A_3]: (m1_subset_1(A_65, B_4) | ~r2_hidden(A_65, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_6, c_122])).
% 2.86/1.47  tff(c_412, plain, (![A_123, B_124]: (m1_subset_1('#skF_2'(A_123, '#skF_5'), B_124) | ~r1_tarski(k1_xboole_0, B_124) | ~r2_hidden(A_123, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_396, c_127])).
% 2.86/1.47  tff(c_415, plain, (![B_124]: (m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')), '#skF_5'), B_124) | ~r1_tarski(k1_xboole_0, B_124) | k2_relat_1('#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_412])).
% 2.86/1.47  tff(c_419, plain, (![B_125]: (m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')), '#skF_5'), B_125) | ~r1_tarski(k1_xboole_0, B_125))), inference(negUnitSimplification, [status(thm)], [c_144, c_415])).
% 2.86/1.47  tff(c_26, plain, (![D_36]: (~r2_hidden(D_36, k1_relset_1('#skF_4', '#skF_3', '#skF_5')) | ~m1_subset_1(D_36, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.86/1.47  tff(c_266, plain, (![D_36]: (~r2_hidden(D_36, k1_xboole_0) | ~m1_subset_1(D_36, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_26])).
% 2.86/1.47  tff(c_404, plain, (![A_122]: (~m1_subset_1('#skF_2'(A_122, '#skF_5'), '#skF_4') | ~r2_hidden(A_122, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_396, c_266])).
% 2.86/1.47  tff(c_408, plain, (~m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')), '#skF_5'), '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_404])).
% 2.86/1.47  tff(c_411, plain, (~m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')), '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_144, c_408])).
% 2.86/1.47  tff(c_422, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_419, c_411])).
% 2.86/1.47  tff(c_453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_276, c_422])).
% 2.86/1.47  tff(c_454, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_61])).
% 2.86/1.47  tff(c_517, plain, (![A_139, B_140, C_141]: (k1_relset_1(A_139, B_140, C_141)=k1_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.86/1.47  tff(c_528, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_517])).
% 2.86/1.47  tff(c_532, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_454, c_528])).
% 2.86/1.47  tff(c_539, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8) | ~v4_relat_1('#skF_5', A_8) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_532, c_12])).
% 2.86/1.47  tff(c_548, plain, (![A_143]: (r1_tarski(k1_xboole_0, A_143) | ~v4_relat_1('#skF_5', A_143))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_539])).
% 2.86/1.47  tff(c_556, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_98, c_548])).
% 2.86/1.47  tff(c_646, plain, (![A_165, B_166, C_167]: (k2_relset_1(A_165, B_166, C_167)=k2_relat_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.86/1.47  tff(c_660, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_646])).
% 2.86/1.47  tff(c_661, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_660, c_28])).
% 2.86/1.47  tff(c_565, plain, (![A_147, B_148]: (r2_hidden('#skF_2'(A_147, B_148), k1_relat_1(B_148)) | ~r2_hidden(A_147, k2_relat_1(B_148)) | ~v1_relat_1(B_148))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.86/1.47  tff(c_570, plain, (![A_147]: (r2_hidden('#skF_2'(A_147, '#skF_5'), k1_xboole_0) | ~r2_hidden(A_147, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_532, c_565])).
% 2.86/1.47  tff(c_574, plain, (![A_149]: (r2_hidden('#skF_2'(A_149, '#skF_5'), k1_xboole_0) | ~r2_hidden(A_149, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_570])).
% 2.86/1.47  tff(c_480, plain, (![A_130, C_131, B_132]: (m1_subset_1(A_130, C_131) | ~m1_subset_1(B_132, k1_zfmisc_1(C_131)) | ~r2_hidden(A_130, B_132))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.86/1.47  tff(c_485, plain, (![A_130, B_4, A_3]: (m1_subset_1(A_130, B_4) | ~r2_hidden(A_130, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_6, c_480])).
% 2.86/1.47  tff(c_682, plain, (![A_171, B_172]: (m1_subset_1('#skF_2'(A_171, '#skF_5'), B_172) | ~r1_tarski(k1_xboole_0, B_172) | ~r2_hidden(A_171, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_574, c_485])).
% 2.86/1.47  tff(c_685, plain, (![B_172]: (m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')), '#skF_5'), B_172) | ~r1_tarski(k1_xboole_0, B_172) | k2_relat_1('#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_682])).
% 2.86/1.47  tff(c_689, plain, (![B_173]: (m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')), '#skF_5'), B_173) | ~r1_tarski(k1_xboole_0, B_173))), inference(negUnitSimplification, [status(thm)], [c_661, c_685])).
% 2.86/1.47  tff(c_456, plain, (![D_36]: (~r2_hidden(D_36, k1_xboole_0) | ~m1_subset_1(D_36, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_454, c_26])).
% 2.86/1.47  tff(c_582, plain, (![A_150]: (~m1_subset_1('#skF_2'(A_150, '#skF_5'), '#skF_4') | ~r2_hidden(A_150, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_574, c_456])).
% 2.86/1.47  tff(c_587, plain, (~m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')), '#skF_5'), '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_582])).
% 2.86/1.47  tff(c_604, plain, (~m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')), '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_587])).
% 2.86/1.47  tff(c_696, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_689, c_604])).
% 2.86/1.47  tff(c_724, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_556, c_696])).
% 2.86/1.47  tff(c_725, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_587])).
% 2.86/1.47  tff(c_744, plain, (![A_175, B_176, C_177]: (k2_relset_1(A_175, B_176, C_177)=k2_relat_1(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.86/1.47  tff(c_755, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_744])).
% 2.86/1.47  tff(c_759, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_725, c_755])).
% 2.86/1.47  tff(c_761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_759])).
% 2.86/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.47  
% 2.86/1.47  Inference rules
% 2.86/1.47  ----------------------
% 2.86/1.47  #Ref     : 0
% 2.86/1.47  #Sup     : 145
% 2.86/1.47  #Fact    : 0
% 2.86/1.47  #Define  : 0
% 2.86/1.47  #Split   : 3
% 2.86/1.47  #Chain   : 0
% 2.86/1.47  #Close   : 0
% 2.86/1.47  
% 2.86/1.47  Ordering : KBO
% 2.86/1.47  
% 2.86/1.47  Simplification rules
% 2.86/1.47  ----------------------
% 2.86/1.47  #Subsume      : 7
% 2.86/1.47  #Demod        : 48
% 2.86/1.47  #Tautology    : 33
% 2.86/1.47  #SimpNegUnit  : 4
% 2.86/1.47  #BackRed      : 10
% 2.86/1.47  
% 2.86/1.47  #Partial instantiations: 0
% 2.86/1.47  #Strategies tried      : 1
% 2.86/1.47  
% 2.86/1.47  Timing (in seconds)
% 2.86/1.47  ----------------------
% 2.86/1.47  Preprocessing        : 0.33
% 2.86/1.47  Parsing              : 0.18
% 2.86/1.47  CNF conversion       : 0.02
% 2.86/1.47  Main loop            : 0.33
% 2.86/1.47  Inferencing          : 0.14
% 2.86/1.47  Reduction            : 0.09
% 2.86/1.47  Demodulation         : 0.06
% 2.86/1.47  BG Simplification    : 0.02
% 2.86/1.47  Subsumption          : 0.05
% 2.86/1.48  Abstraction          : 0.02
% 2.86/1.48  MUC search           : 0.00
% 2.86/1.48  Cooper               : 0.00
% 2.86/1.48  Total                : 0.70
% 2.86/1.48  Index Insertion      : 0.00
% 2.86/1.48  Index Deletion       : 0.00
% 2.86/1.48  Index Matching       : 0.00
% 2.86/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
