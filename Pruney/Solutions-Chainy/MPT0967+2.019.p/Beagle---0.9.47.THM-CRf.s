%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:15 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 440 expanded)
%              Number of leaves         :   32 ( 152 expanded)
%              Depth                    :    9
%              Number of atoms          :  250 (1419 expanded)
%              Number of equality atoms :   53 ( 424 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_76,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_560,plain,(
    ! [C_120,A_121,B_122] :
      ( v1_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_564,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_560])).

tff(c_577,plain,(
    ! [C_129,B_130,A_131] :
      ( v5_relat_1(C_129,B_130)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_131,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_581,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_577])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_46,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_582,plain,(
    ! [C_132,B_133,A_134] :
      ( r2_hidden(C_132,B_133)
      | ~ r2_hidden(C_132,A_134)
      | ~ r1_tarski(A_134,B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_597,plain,(
    ! [A_138,B_139,B_140] :
      ( r2_hidden('#skF_1'(A_138,B_139),B_140)
      | ~ r1_tarski(A_138,B_140)
      | r1_tarski(A_138,B_139) ) ),
    inference(resolution,[status(thm)],[c_6,c_582])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_653,plain,(
    ! [A_154,B_155,B_156,B_157] :
      ( r2_hidden('#skF_1'(A_154,B_155),B_156)
      | ~ r1_tarski(B_157,B_156)
      | ~ r1_tarski(A_154,B_157)
      | r1_tarski(A_154,B_155) ) ),
    inference(resolution,[status(thm)],[c_597,c_2])).

tff(c_709,plain,(
    ! [A_169,B_170] :
      ( r2_hidden('#skF_1'(A_169,B_170),'#skF_4')
      | ~ r1_tarski(A_169,'#skF_3')
      | r1_tarski(A_169,B_170) ) ),
    inference(resolution,[status(thm)],[c_46,c_653])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_718,plain,(
    ! [A_171] :
      ( ~ r1_tarski(A_171,'#skF_3')
      | r1_tarski(A_171,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_709,c_4])).

tff(c_736,plain,(
    ! [B_9] :
      ( r1_tarski(k2_relat_1(B_9),'#skF_4')
      | ~ v5_relat_1(B_9,'#skF_3')
      | ~ v1_relat_1(B_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_718])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_607,plain,(
    ! [A_142,B_143,C_144] :
      ( k1_relset_1(A_142,B_143,C_144) = k1_relat_1(C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_611,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_607])).

tff(c_885,plain,(
    ! [B_193,A_194,C_195] :
      ( k1_xboole_0 = B_193
      | k1_relset_1(A_194,B_193,C_195) = A_194
      | ~ v1_funct_2(C_195,A_194,B_193)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_194,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_891,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_885])).

tff(c_895,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_611,c_891])).

tff(c_896,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_895])).

tff(c_36,plain,(
    ! [B_23,A_22] :
      ( m1_subset_1(B_23,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_23),A_22)))
      | ~ r1_tarski(k2_relat_1(B_23),A_22)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_916,plain,(
    ! [A_22] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_22)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_22)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_896,c_36])).

tff(c_1008,plain,(
    ! [A_202] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_202)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_52,c_916])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_42])).

tff(c_65,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_66,plain,(
    ! [C_28,A_29,B_30] :
      ( v1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_70,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_66])).

tff(c_107,plain,(
    ! [C_43,B_44,A_45] :
      ( v5_relat_1(C_43,B_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_45,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_111,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_107])).

tff(c_112,plain,(
    ! [C_46,B_47,A_48] :
      ( r2_hidden(C_46,B_47)
      | ~ r2_hidden(C_46,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_116,plain,(
    ! [A_49,B_50,B_51] :
      ( r2_hidden('#skF_1'(A_49,B_50),B_51)
      | ~ r1_tarski(A_49,B_51)
      | r1_tarski(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_6,c_112])).

tff(c_137,plain,(
    ! [A_60,B_61,B_62,B_63] :
      ( r2_hidden('#skF_1'(A_60,B_61),B_62)
      | ~ r1_tarski(B_63,B_62)
      | ~ r1_tarski(A_60,B_63)
      | r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_116,c_2])).

tff(c_193,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_1'(A_75,B_76),'#skF_4')
      | ~ r1_tarski(A_75,'#skF_3')
      | r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_46,c_137])).

tff(c_202,plain,(
    ! [A_77] :
      ( ~ r1_tarski(A_77,'#skF_3')
      | r1_tarski(A_77,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_193,c_4])).

tff(c_220,plain,(
    ! [B_9] :
      ( r1_tarski(k2_relat_1(B_9),'#skF_4')
      | ~ v5_relat_1(B_9,'#skF_3')
      | ~ v1_relat_1(B_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_202])).

tff(c_125,plain,(
    ! [A_52,B_53,C_54] :
      ( k1_relset_1(A_52,B_53,C_54) = k1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_129,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_125])).

tff(c_448,plain,(
    ! [B_112,A_113,C_114] :
      ( k1_xboole_0 = B_112
      | k1_relset_1(A_113,B_112,C_114) = A_113
      | ~ v1_funct_2(C_114,A_113,B_112)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_454,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_448])).

tff(c_458,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_129,c_454])).

tff(c_459,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_458])).

tff(c_38,plain,(
    ! [B_23,A_22] :
      ( v1_funct_2(B_23,k1_relat_1(B_23),A_22)
      | ~ r1_tarski(k2_relat_1(B_23),A_22)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_482,plain,(
    ! [A_22] :
      ( v1_funct_2('#skF_5','#skF_2',A_22)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_22)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_38])).

tff(c_523,plain,(
    ! [A_116] :
      ( v1_funct_2('#skF_5','#skF_2',A_116)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_52,c_482])).

tff(c_527,plain,
    ( v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_220,c_523])).

tff(c_542,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_111,c_527])).

tff(c_544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_542])).

tff(c_545,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1044,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1008,c_545])).

tff(c_1047,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_736,c_1044])).

tff(c_1057,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_581,c_1047])).

tff(c_1059,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1058,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1065,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1059,c_1058])).

tff(c_1086,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1065,c_48])).

tff(c_1291,plain,(
    ! [C_254,A_255,B_256] :
      ( v1_relat_1(C_254)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1295,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1086,c_1291])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1060,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1058,c_8])).

tff(c_1075,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1065,c_1060])).

tff(c_1308,plain,(
    ! [C_263,B_264,A_265] :
      ( v5_relat_1(C_263,B_264)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_265,B_264))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1312,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_1086,c_1308])).

tff(c_1296,plain,(
    ! [B_257,A_258] :
      ( r1_tarski(k2_relat_1(B_257),A_258)
      | ~ v5_relat_1(B_257,A_258)
      | ~ v1_relat_1(B_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1078,plain,(
    ! [A_7] :
      ( A_7 = '#skF_3'
      | ~ r1_tarski(A_7,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1059,c_1059,c_10])).

tff(c_1301,plain,(
    ! [B_257] :
      ( k2_relat_1(B_257) = '#skF_3'
      | ~ v5_relat_1(B_257,'#skF_3')
      | ~ v1_relat_1(B_257) ) ),
    inference(resolution,[status(thm)],[c_1296,c_1078])).

tff(c_1315,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1312,c_1301])).

tff(c_1318,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1295,c_1315])).

tff(c_1070,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1065,c_50])).

tff(c_1371,plain,(
    ! [A_276,B_277,C_278] :
      ( k1_relset_1(A_276,B_277,C_278) = k1_relat_1(C_278)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1375,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1086,c_1371])).

tff(c_32,plain,(
    ! [B_20,C_21] :
      ( k1_relset_1(k1_xboole_0,B_20,C_21) = k1_xboole_0
      | ~ v1_funct_2(C_21,k1_xboole_0,B_20)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1456,plain,(
    ! [B_297,C_298] :
      ( k1_relset_1('#skF_3',B_297,C_298) = '#skF_3'
      | ~ v1_funct_2(C_298,'#skF_3',B_297)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_297))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1059,c_1059,c_1059,c_1059,c_32])).

tff(c_1459,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1086,c_1456])).

tff(c_1462,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1070,c_1375,c_1459])).

tff(c_1480,plain,(
    ! [B_300,A_301] :
      ( m1_subset_1(B_300,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_300),A_301)))
      | ~ r1_tarski(k2_relat_1(B_300),A_301)
      | ~ v1_funct_1(B_300)
      | ~ v1_relat_1(B_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1503,plain,(
    ! [A_301] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_301)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_301)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1462,c_1480])).

tff(c_1511,plain,(
    ! [A_301] : m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_301))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1295,c_52,c_1075,c_1318,c_1503])).

tff(c_1103,plain,(
    ! [C_210,A_211,B_212] :
      ( v1_relat_1(C_210)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1107,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1086,c_1103])).

tff(c_1130,plain,(
    ! [C_221,B_222,A_223] :
      ( v5_relat_1(C_221,B_222)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_223,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1134,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_1086,c_1130])).

tff(c_1113,plain,(
    ! [B_216,A_217] :
      ( r1_tarski(k2_relat_1(B_216),A_217)
      | ~ v5_relat_1(B_216,A_217)
      | ~ v1_relat_1(B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1118,plain,(
    ! [B_216] :
      ( k2_relat_1(B_216) = '#skF_3'
      | ~ v5_relat_1(B_216,'#skF_3')
      | ~ v1_relat_1(B_216) ) ),
    inference(resolution,[status(thm)],[c_1113,c_1078])).

tff(c_1137,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1134,c_1118])).

tff(c_1140,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1107,c_1137])).

tff(c_1174,plain,(
    ! [A_229,B_230,C_231] :
      ( k1_relset_1(A_229,B_230,C_231) = k1_relat_1(C_231)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1178,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1086,c_1174])).

tff(c_1261,plain,(
    ! [B_251,C_252] :
      ( k1_relset_1('#skF_3',B_251,C_252) = '#skF_3'
      | ~ v1_funct_2(C_252,'#skF_3',B_251)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_251))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1059,c_1059,c_1059,c_1059,c_32])).

tff(c_1264,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1086,c_1261])).

tff(c_1267,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1070,c_1178,c_1264])).

tff(c_1272,plain,(
    ! [A_22] :
      ( v1_funct_2('#skF_5','#skF_3',A_22)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_22)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1267,c_38])).

tff(c_1276,plain,(
    ! [A_22] : v1_funct_2('#skF_5','#skF_3',A_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1107,c_52,c_1075,c_1140,c_1272])).

tff(c_1094,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1065,c_1065,c_54])).

tff(c_1095,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1094])).

tff(c_1281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1276,c_1095])).

tff(c_1282,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1094])).

tff(c_1515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1511,c_1282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:20:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.58  
% 3.44/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.58  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.44/1.58  
% 3.44/1.58  %Foreground sorts:
% 3.44/1.58  
% 3.44/1.58  
% 3.44/1.58  %Background operators:
% 3.44/1.58  
% 3.44/1.58  
% 3.44/1.58  %Foreground operators:
% 3.44/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.44/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.44/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.44/1.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.44/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.44/1.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.44/1.58  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.44/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.44/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.44/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.44/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.44/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.44/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.44/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.44/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.44/1.58  
% 3.44/1.60  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 3.44/1.60  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.44/1.60  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.44/1.60  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.44/1.60  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.44/1.60  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.44/1.60  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.44/1.60  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 3.44/1.60  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.44/1.60  tff(f_38, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.44/1.60  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.44/1.60  tff(c_560, plain, (![C_120, A_121, B_122]: (v1_relat_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.44/1.60  tff(c_564, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_560])).
% 3.44/1.60  tff(c_577, plain, (![C_129, B_130, A_131]: (v5_relat_1(C_129, B_130) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_131, B_130))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.44/1.60  tff(c_581, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_577])).
% 3.44/1.60  tff(c_14, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.44/1.60  tff(c_46, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.44/1.60  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.44/1.60  tff(c_582, plain, (![C_132, B_133, A_134]: (r2_hidden(C_132, B_133) | ~r2_hidden(C_132, A_134) | ~r1_tarski(A_134, B_133))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.44/1.60  tff(c_597, plain, (![A_138, B_139, B_140]: (r2_hidden('#skF_1'(A_138, B_139), B_140) | ~r1_tarski(A_138, B_140) | r1_tarski(A_138, B_139))), inference(resolution, [status(thm)], [c_6, c_582])).
% 3.44/1.60  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.44/1.60  tff(c_653, plain, (![A_154, B_155, B_156, B_157]: (r2_hidden('#skF_1'(A_154, B_155), B_156) | ~r1_tarski(B_157, B_156) | ~r1_tarski(A_154, B_157) | r1_tarski(A_154, B_155))), inference(resolution, [status(thm)], [c_597, c_2])).
% 3.44/1.60  tff(c_709, plain, (![A_169, B_170]: (r2_hidden('#skF_1'(A_169, B_170), '#skF_4') | ~r1_tarski(A_169, '#skF_3') | r1_tarski(A_169, B_170))), inference(resolution, [status(thm)], [c_46, c_653])).
% 3.44/1.60  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.44/1.60  tff(c_718, plain, (![A_171]: (~r1_tarski(A_171, '#skF_3') | r1_tarski(A_171, '#skF_4'))), inference(resolution, [status(thm)], [c_709, c_4])).
% 3.44/1.60  tff(c_736, plain, (![B_9]: (r1_tarski(k2_relat_1(B_9), '#skF_4') | ~v5_relat_1(B_9, '#skF_3') | ~v1_relat_1(B_9))), inference(resolution, [status(thm)], [c_14, c_718])).
% 3.44/1.60  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.44/1.60  tff(c_44, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.44/1.60  tff(c_56, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_44])).
% 3.44/1.60  tff(c_50, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.44/1.60  tff(c_607, plain, (![A_142, B_143, C_144]: (k1_relset_1(A_142, B_143, C_144)=k1_relat_1(C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.44/1.60  tff(c_611, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_607])).
% 3.44/1.60  tff(c_885, plain, (![B_193, A_194, C_195]: (k1_xboole_0=B_193 | k1_relset_1(A_194, B_193, C_195)=A_194 | ~v1_funct_2(C_195, A_194, B_193) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_194, B_193))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.44/1.60  tff(c_891, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_885])).
% 3.44/1.60  tff(c_895, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_611, c_891])).
% 3.44/1.60  tff(c_896, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_56, c_895])).
% 3.44/1.60  tff(c_36, plain, (![B_23, A_22]: (m1_subset_1(B_23, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_23), A_22))) | ~r1_tarski(k2_relat_1(B_23), A_22) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.44/1.60  tff(c_916, plain, (![A_22]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_22))) | ~r1_tarski(k2_relat_1('#skF_5'), A_22) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_896, c_36])).
% 3.44/1.60  tff(c_1008, plain, (![A_202]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_202))) | ~r1_tarski(k2_relat_1('#skF_5'), A_202))), inference(demodulation, [status(thm), theory('equality')], [c_564, c_52, c_916])).
% 3.44/1.60  tff(c_42, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.44/1.60  tff(c_54, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_42])).
% 3.44/1.60  tff(c_65, plain, (~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 3.44/1.60  tff(c_66, plain, (![C_28, A_29, B_30]: (v1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.44/1.60  tff(c_70, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_66])).
% 3.44/1.60  tff(c_107, plain, (![C_43, B_44, A_45]: (v5_relat_1(C_43, B_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_45, B_44))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.44/1.60  tff(c_111, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_107])).
% 3.44/1.60  tff(c_112, plain, (![C_46, B_47, A_48]: (r2_hidden(C_46, B_47) | ~r2_hidden(C_46, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.44/1.60  tff(c_116, plain, (![A_49, B_50, B_51]: (r2_hidden('#skF_1'(A_49, B_50), B_51) | ~r1_tarski(A_49, B_51) | r1_tarski(A_49, B_50))), inference(resolution, [status(thm)], [c_6, c_112])).
% 3.44/1.60  tff(c_137, plain, (![A_60, B_61, B_62, B_63]: (r2_hidden('#skF_1'(A_60, B_61), B_62) | ~r1_tarski(B_63, B_62) | ~r1_tarski(A_60, B_63) | r1_tarski(A_60, B_61))), inference(resolution, [status(thm)], [c_116, c_2])).
% 3.44/1.60  tff(c_193, plain, (![A_75, B_76]: (r2_hidden('#skF_1'(A_75, B_76), '#skF_4') | ~r1_tarski(A_75, '#skF_3') | r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_46, c_137])).
% 3.44/1.60  tff(c_202, plain, (![A_77]: (~r1_tarski(A_77, '#skF_3') | r1_tarski(A_77, '#skF_4'))), inference(resolution, [status(thm)], [c_193, c_4])).
% 3.44/1.60  tff(c_220, plain, (![B_9]: (r1_tarski(k2_relat_1(B_9), '#skF_4') | ~v5_relat_1(B_9, '#skF_3') | ~v1_relat_1(B_9))), inference(resolution, [status(thm)], [c_14, c_202])).
% 3.44/1.60  tff(c_125, plain, (![A_52, B_53, C_54]: (k1_relset_1(A_52, B_53, C_54)=k1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.44/1.61  tff(c_129, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_125])).
% 3.44/1.61  tff(c_448, plain, (![B_112, A_113, C_114]: (k1_xboole_0=B_112 | k1_relset_1(A_113, B_112, C_114)=A_113 | ~v1_funct_2(C_114, A_113, B_112) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.44/1.61  tff(c_454, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_448])).
% 3.44/1.61  tff(c_458, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_129, c_454])).
% 3.44/1.61  tff(c_459, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_56, c_458])).
% 3.44/1.61  tff(c_38, plain, (![B_23, A_22]: (v1_funct_2(B_23, k1_relat_1(B_23), A_22) | ~r1_tarski(k2_relat_1(B_23), A_22) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.44/1.61  tff(c_482, plain, (![A_22]: (v1_funct_2('#skF_5', '#skF_2', A_22) | ~r1_tarski(k2_relat_1('#skF_5'), A_22) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_459, c_38])).
% 3.44/1.61  tff(c_523, plain, (![A_116]: (v1_funct_2('#skF_5', '#skF_2', A_116) | ~r1_tarski(k2_relat_1('#skF_5'), A_116))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_52, c_482])).
% 3.44/1.61  tff(c_527, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_220, c_523])).
% 3.44/1.61  tff(c_542, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_111, c_527])).
% 3.44/1.61  tff(c_544, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_542])).
% 3.44/1.61  tff(c_545, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_54])).
% 3.44/1.61  tff(c_1044, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_1008, c_545])).
% 3.44/1.61  tff(c_1047, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_736, c_1044])).
% 3.44/1.61  tff(c_1057, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_564, c_581, c_1047])).
% 3.44/1.61  tff(c_1059, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 3.44/1.61  tff(c_1058, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_44])).
% 3.44/1.61  tff(c_1065, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1059, c_1058])).
% 3.44/1.61  tff(c_1086, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1065, c_48])).
% 3.44/1.61  tff(c_1291, plain, (![C_254, A_255, B_256]: (v1_relat_1(C_254) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.44/1.61  tff(c_1295, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1086, c_1291])).
% 3.44/1.61  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.44/1.61  tff(c_1060, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1058, c_8])).
% 3.44/1.61  tff(c_1075, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1065, c_1060])).
% 3.44/1.61  tff(c_1308, plain, (![C_263, B_264, A_265]: (v5_relat_1(C_263, B_264) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_265, B_264))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.44/1.61  tff(c_1312, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_1086, c_1308])).
% 3.44/1.61  tff(c_1296, plain, (![B_257, A_258]: (r1_tarski(k2_relat_1(B_257), A_258) | ~v5_relat_1(B_257, A_258) | ~v1_relat_1(B_257))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.44/1.61  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.44/1.61  tff(c_1078, plain, (![A_7]: (A_7='#skF_3' | ~r1_tarski(A_7, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1059, c_1059, c_10])).
% 3.44/1.61  tff(c_1301, plain, (![B_257]: (k2_relat_1(B_257)='#skF_3' | ~v5_relat_1(B_257, '#skF_3') | ~v1_relat_1(B_257))), inference(resolution, [status(thm)], [c_1296, c_1078])).
% 3.44/1.61  tff(c_1315, plain, (k2_relat_1('#skF_5')='#skF_3' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1312, c_1301])).
% 3.44/1.61  tff(c_1318, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1295, c_1315])).
% 3.44/1.61  tff(c_1070, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1065, c_50])).
% 3.44/1.61  tff(c_1371, plain, (![A_276, B_277, C_278]: (k1_relset_1(A_276, B_277, C_278)=k1_relat_1(C_278) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.44/1.61  tff(c_1375, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1086, c_1371])).
% 3.44/1.61  tff(c_32, plain, (![B_20, C_21]: (k1_relset_1(k1_xboole_0, B_20, C_21)=k1_xboole_0 | ~v1_funct_2(C_21, k1_xboole_0, B_20) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_20))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.44/1.61  tff(c_1456, plain, (![B_297, C_298]: (k1_relset_1('#skF_3', B_297, C_298)='#skF_3' | ~v1_funct_2(C_298, '#skF_3', B_297) | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_297))))), inference(demodulation, [status(thm), theory('equality')], [c_1059, c_1059, c_1059, c_1059, c_32])).
% 3.44/1.61  tff(c_1459, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1086, c_1456])).
% 3.44/1.61  tff(c_1462, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1070, c_1375, c_1459])).
% 3.44/1.61  tff(c_1480, plain, (![B_300, A_301]: (m1_subset_1(B_300, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_300), A_301))) | ~r1_tarski(k2_relat_1(B_300), A_301) | ~v1_funct_1(B_300) | ~v1_relat_1(B_300))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.44/1.61  tff(c_1503, plain, (![A_301]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_301))) | ~r1_tarski(k2_relat_1('#skF_5'), A_301) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1462, c_1480])).
% 3.44/1.61  tff(c_1511, plain, (![A_301]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_301))))), inference(demodulation, [status(thm), theory('equality')], [c_1295, c_52, c_1075, c_1318, c_1503])).
% 3.44/1.61  tff(c_1103, plain, (![C_210, A_211, B_212]: (v1_relat_1(C_210) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.44/1.61  tff(c_1107, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1086, c_1103])).
% 3.44/1.61  tff(c_1130, plain, (![C_221, B_222, A_223]: (v5_relat_1(C_221, B_222) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_223, B_222))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.44/1.61  tff(c_1134, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_1086, c_1130])).
% 3.44/1.61  tff(c_1113, plain, (![B_216, A_217]: (r1_tarski(k2_relat_1(B_216), A_217) | ~v5_relat_1(B_216, A_217) | ~v1_relat_1(B_216))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.44/1.61  tff(c_1118, plain, (![B_216]: (k2_relat_1(B_216)='#skF_3' | ~v5_relat_1(B_216, '#skF_3') | ~v1_relat_1(B_216))), inference(resolution, [status(thm)], [c_1113, c_1078])).
% 3.44/1.61  tff(c_1137, plain, (k2_relat_1('#skF_5')='#skF_3' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1134, c_1118])).
% 3.44/1.61  tff(c_1140, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1107, c_1137])).
% 3.44/1.61  tff(c_1174, plain, (![A_229, B_230, C_231]: (k1_relset_1(A_229, B_230, C_231)=k1_relat_1(C_231) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.44/1.61  tff(c_1178, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1086, c_1174])).
% 3.44/1.61  tff(c_1261, plain, (![B_251, C_252]: (k1_relset_1('#skF_3', B_251, C_252)='#skF_3' | ~v1_funct_2(C_252, '#skF_3', B_251) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_251))))), inference(demodulation, [status(thm), theory('equality')], [c_1059, c_1059, c_1059, c_1059, c_32])).
% 3.44/1.61  tff(c_1264, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1086, c_1261])).
% 3.44/1.61  tff(c_1267, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1070, c_1178, c_1264])).
% 3.44/1.61  tff(c_1272, plain, (![A_22]: (v1_funct_2('#skF_5', '#skF_3', A_22) | ~r1_tarski(k2_relat_1('#skF_5'), A_22) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1267, c_38])).
% 3.44/1.61  tff(c_1276, plain, (![A_22]: (v1_funct_2('#skF_5', '#skF_3', A_22))), inference(demodulation, [status(thm), theory('equality')], [c_1107, c_52, c_1075, c_1140, c_1272])).
% 3.44/1.61  tff(c_1094, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1065, c_1065, c_54])).
% 3.44/1.61  tff(c_1095, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_1094])).
% 3.44/1.61  tff(c_1281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1276, c_1095])).
% 3.44/1.61  tff(c_1282, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_1094])).
% 3.44/1.61  tff(c_1515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1511, c_1282])).
% 3.44/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.61  
% 3.44/1.61  Inference rules
% 3.44/1.61  ----------------------
% 3.44/1.61  #Ref     : 0
% 3.44/1.61  #Sup     : 315
% 3.44/1.61  #Fact    : 0
% 3.44/1.61  #Define  : 0
% 3.44/1.61  #Split   : 6
% 3.44/1.61  #Chain   : 0
% 3.44/1.61  #Close   : 0
% 3.44/1.61  
% 3.44/1.61  Ordering : KBO
% 3.44/1.61  
% 3.44/1.61  Simplification rules
% 3.44/1.61  ----------------------
% 3.44/1.61  #Subsume      : 50
% 3.44/1.61  #Demod        : 175
% 3.44/1.61  #Tautology    : 135
% 3.44/1.61  #SimpNegUnit  : 5
% 3.44/1.61  #BackRed      : 9
% 3.44/1.61  
% 3.44/1.61  #Partial instantiations: 0
% 3.44/1.61  #Strategies tried      : 1
% 3.44/1.61  
% 3.44/1.61  Timing (in seconds)
% 3.44/1.61  ----------------------
% 3.44/1.61  Preprocessing        : 0.32
% 3.44/1.61  Parsing              : 0.17
% 3.44/1.61  CNF conversion       : 0.02
% 3.44/1.61  Main loop            : 0.50
% 3.44/1.61  Inferencing          : 0.20
% 3.44/1.61  Reduction            : 0.14
% 3.44/1.61  Demodulation         : 0.09
% 3.44/1.61  BG Simplification    : 0.02
% 3.44/1.61  Subsumption          : 0.09
% 3.44/1.61  Abstraction          : 0.02
% 3.44/1.61  MUC search           : 0.00
% 3.44/1.61  Cooper               : 0.00
% 3.44/1.61  Total                : 0.86
% 3.44/1.61  Index Insertion      : 0.00
% 3.44/1.61  Index Deletion       : 0.00
% 3.44/1.61  Index Matching       : 0.00
% 3.44/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
