%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:16 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 480 expanded)
%              Number of leaves         :   33 ( 164 expanded)
%              Depth                    :   10
%              Number of atoms          :  262 (1505 expanded)
%              Number of equality atoms :   55 ( 436 expanded)
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

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_115,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_83,axiom,(
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

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_22,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_551,plain,(
    ! [B_126,A_127] :
      ( v1_relat_1(B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_127))
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_554,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_551])).

tff(c_557,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_554])).

tff(c_576,plain,(
    ! [C_133,B_134,A_135] :
      ( v5_relat_1(C_133,B_134)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_135,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_580,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_576])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_586,plain,(
    ! [C_139,B_140,A_141] :
      ( r2_hidden(C_139,B_140)
      | ~ r2_hidden(C_139,A_141)
      | ~ r1_tarski(A_141,B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_602,plain,(
    ! [A_146,B_147,B_148] :
      ( r2_hidden('#skF_1'(A_146,B_147),B_148)
      | ~ r1_tarski(A_146,B_148)
      | r1_tarski(A_146,B_147) ) ),
    inference(resolution,[status(thm)],[c_6,c_586])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_639,plain,(
    ! [A_158,B_159,B_160,B_161] :
      ( r2_hidden('#skF_1'(A_158,B_159),B_160)
      | ~ r1_tarski(B_161,B_160)
      | ~ r1_tarski(A_158,B_161)
      | r1_tarski(A_158,B_159) ) ),
    inference(resolution,[status(thm)],[c_602,c_2])).

tff(c_676,plain,(
    ! [A_167,B_168] :
      ( r2_hidden('#skF_1'(A_167,B_168),'#skF_4')
      | ~ r1_tarski(A_167,'#skF_3')
      | r1_tarski(A_167,B_168) ) ),
    inference(resolution,[status(thm)],[c_52,c_639])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_685,plain,(
    ! [A_169] :
      ( ~ r1_tarski(A_169,'#skF_3')
      | r1_tarski(A_169,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_676,c_4])).

tff(c_698,plain,(
    ! [B_13] :
      ( r1_tarski(k2_relat_1(B_13),'#skF_4')
      | ~ v5_relat_1(B_13,'#skF_3')
      | ~ v1_relat_1(B_13) ) ),
    inference(resolution,[status(thm)],[c_20,c_685])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_65,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_611,plain,(
    ! [A_149,B_150,C_151] :
      ( k1_relset_1(A_149,B_150,C_151) = k1_relat_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_615,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_611])).

tff(c_998,plain,(
    ! [B_219,A_220,C_221] :
      ( k1_xboole_0 = B_219
      | k1_relset_1(A_220,B_219,C_221) = A_220
      | ~ v1_funct_2(C_221,A_220,B_219)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_220,B_219))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1004,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_998])).

tff(c_1008,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_615,c_1004])).

tff(c_1009,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_1008])).

tff(c_42,plain,(
    ! [B_26,A_25] :
      ( m1_subset_1(B_26,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_26),A_25)))
      | ~ r1_tarski(k2_relat_1(B_26),A_25)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1029,plain,(
    ! [A_25] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_25)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_25)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1009,c_42])).

tff(c_1120,plain,(
    ! [A_226] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_226)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_58,c_1029])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_60,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_48])).

tff(c_66,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_67,plain,(
    ! [B_31,A_32] :
      ( v1_relat_1(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_32))
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_67])).

tff(c_73,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_70])).

tff(c_119,plain,(
    ! [C_43,B_44,A_45] :
      ( v5_relat_1(C_43,B_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_45,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_123,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_119])).

tff(c_124,plain,(
    ! [C_46,B_47,A_48] :
      ( r2_hidden(C_46,B_47)
      | ~ r2_hidden(C_46,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_144,plain,(
    ! [A_55,B_56,B_57] :
      ( r2_hidden('#skF_1'(A_55,B_56),B_57)
      | ~ r1_tarski(A_55,B_57)
      | r1_tarski(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_124])).

tff(c_183,plain,(
    ! [A_70,B_71,B_72,B_73] :
      ( r2_hidden('#skF_1'(A_70,B_71),B_72)
      | ~ r1_tarski(B_73,B_72)
      | ~ r1_tarski(A_70,B_73)
      | r1_tarski(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_144,c_2])).

tff(c_220,plain,(
    ! [A_79,B_80] :
      ( r2_hidden('#skF_1'(A_79,B_80),'#skF_4')
      | ~ r1_tarski(A_79,'#skF_3')
      | r1_tarski(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_52,c_183])).

tff(c_229,plain,(
    ! [A_81] :
      ( ~ r1_tarski(A_81,'#skF_3')
      | r1_tarski(A_81,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_220,c_4])).

tff(c_242,plain,(
    ! [B_13] :
      ( r1_tarski(k2_relat_1(B_13),'#skF_4')
      | ~ v5_relat_1(B_13,'#skF_3')
      | ~ v1_relat_1(B_13) ) ),
    inference(resolution,[status(thm)],[c_20,c_229])).

tff(c_154,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_158,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_154])).

tff(c_450,plain,(
    ! [B_117,A_118,C_119] :
      ( k1_xboole_0 = B_117
      | k1_relset_1(A_118,B_117,C_119) = A_118
      | ~ v1_funct_2(C_119,A_118,B_117)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_456,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_450])).

tff(c_460,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_158,c_456])).

tff(c_461,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_460])).

tff(c_44,plain,(
    ! [B_26,A_25] :
      ( v1_funct_2(B_26,k1_relat_1(B_26),A_25)
      | ~ r1_tarski(k2_relat_1(B_26),A_25)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_478,plain,(
    ! [A_25] :
      ( v1_funct_2('#skF_5','#skF_2',A_25)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_25)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_44])).

tff(c_500,plain,(
    ! [A_120] :
      ( v1_funct_2('#skF_5','#skF_2',A_120)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_58,c_478])).

tff(c_504,plain,
    ( v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_242,c_500])).

tff(c_519,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_123,c_504])).

tff(c_521,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_519])).

tff(c_522,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1157,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1120,c_522])).

tff(c_1160,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_698,c_1157])).

tff(c_1170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_580,c_1160])).

tff(c_1172,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1171,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1178,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1172,c_1171])).

tff(c_1183,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1178,c_54])).

tff(c_1192,plain,(
    ! [B_228,A_229] :
      ( v1_relat_1(B_228)
      | ~ m1_subset_1(B_228,k1_zfmisc_1(A_229))
      | ~ v1_relat_1(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1195,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1183,c_1192])).

tff(c_1198,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1195])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1173,plain,(
    ! [A_8] : r1_tarski('#skF_2',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1171,c_14])).

tff(c_1189,plain,(
    ! [A_8] : r1_tarski('#skF_3',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1178,c_1173])).

tff(c_1594,plain,(
    ! [C_304,B_305,A_306] :
      ( v5_relat_1(C_304,B_305)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(k2_zfmisc_1(A_306,B_305))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1598,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_1183,c_1594])).

tff(c_1568,plain,(
    ! [B_295,A_296] :
      ( r1_tarski(k2_relat_1(B_295),A_296)
      | ~ v5_relat_1(B_295,A_296)
      | ~ v1_relat_1(B_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1545,plain,(
    ! [B_292,A_293] :
      ( B_292 = A_293
      | ~ r1_tarski(B_292,A_293)
      | ~ r1_tarski(A_293,B_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1550,plain,(
    ! [A_8] :
      ( A_8 = '#skF_3'
      | ~ r1_tarski(A_8,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1189,c_1545])).

tff(c_1575,plain,(
    ! [B_295] :
      ( k2_relat_1(B_295) = '#skF_3'
      | ~ v5_relat_1(B_295,'#skF_3')
      | ~ v1_relat_1(B_295) ) ),
    inference(resolution,[status(thm)],[c_1568,c_1550])).

tff(c_1601,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1598,c_1575])).

tff(c_1604,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1198,c_1601])).

tff(c_1184,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1178,c_56])).

tff(c_1646,plain,(
    ! [A_314,B_315,C_316] :
      ( k1_relset_1(A_314,B_315,C_316) = k1_relat_1(C_316)
      | ~ m1_subset_1(C_316,k1_zfmisc_1(k2_zfmisc_1(A_314,B_315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1650,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1183,c_1646])).

tff(c_38,plain,(
    ! [B_23,C_24] :
      ( k1_relset_1(k1_xboole_0,B_23,C_24) = k1_xboole_0
      | ~ v1_funct_2(C_24,k1_xboole_0,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1805,plain,(
    ! [B_342,C_343] :
      ( k1_relset_1('#skF_3',B_342,C_343) = '#skF_3'
      | ~ v1_funct_2(C_343,'#skF_3',B_342)
      | ~ m1_subset_1(C_343,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_342))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1172,c_1172,c_1172,c_1172,c_38])).

tff(c_1808,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1183,c_1805])).

tff(c_1811,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1184,c_1650,c_1808])).

tff(c_1821,plain,(
    ! [A_25] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_25)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_25)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1811,c_42])).

tff(c_1830,plain,(
    ! [A_25] : m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_25))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1198,c_58,c_1189,c_1604,c_1821])).

tff(c_1232,plain,(
    ! [C_237,B_238,A_239] :
      ( v5_relat_1(C_237,B_238)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_239,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1236,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_1183,c_1232])).

tff(c_1237,plain,(
    ! [B_240,A_241] :
      ( r1_tarski(k2_relat_1(B_240),A_241)
      | ~ v5_relat_1(B_240,A_241)
      | ~ v1_relat_1(B_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1209,plain,(
    ! [B_234,A_235] :
      ( B_234 = A_235
      | ~ r1_tarski(B_234,A_235)
      | ~ r1_tarski(A_235,B_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1214,plain,(
    ! [A_8] :
      ( A_8 = '#skF_3'
      | ~ r1_tarski(A_8,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1189,c_1209])).

tff(c_1246,plain,(
    ! [B_242] :
      ( k2_relat_1(B_242) = '#skF_3'
      | ~ v5_relat_1(B_242,'#skF_3')
      | ~ v1_relat_1(B_242) ) ),
    inference(resolution,[status(thm)],[c_1237,c_1214])).

tff(c_1249,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1236,c_1246])).

tff(c_1252,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1198,c_1249])).

tff(c_1312,plain,(
    ! [A_257,B_258,C_259] :
      ( k1_relset_1(A_257,B_258,C_259) = k1_relat_1(C_259)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1316,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1183,c_1312])).

tff(c_1510,plain,(
    ! [B_290,C_291] :
      ( k1_relset_1('#skF_3',B_290,C_291) = '#skF_3'
      | ~ v1_funct_2(C_291,'#skF_3',B_290)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_290))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1172,c_1172,c_1172,c_1172,c_38])).

tff(c_1513,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1183,c_1510])).

tff(c_1516,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1184,c_1316,c_1513])).

tff(c_1529,plain,(
    ! [A_25] :
      ( v1_funct_2('#skF_5','#skF_3',A_25)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_25)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1516,c_44])).

tff(c_1537,plain,(
    ! [A_25] : v1_funct_2('#skF_5','#skF_3',A_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1198,c_58,c_1189,c_1252,c_1529])).

tff(c_1207,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1178,c_1178,c_60])).

tff(c_1208,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1207])).

tff(c_1542,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1537,c_1208])).

tff(c_1543,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1207])).

tff(c_1844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1830,c_1543])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:28:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.70  
% 4.01/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.70  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.01/1.70  
% 4.01/1.70  %Foreground sorts:
% 4.01/1.70  
% 4.01/1.70  
% 4.01/1.70  %Background operators:
% 4.01/1.70  
% 4.01/1.70  
% 4.01/1.70  %Foreground operators:
% 4.01/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.01/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.01/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.01/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.01/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.01/1.70  tff('#skF_5', type, '#skF_5': $i).
% 4.01/1.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.01/1.70  tff('#skF_2', type, '#skF_2': $i).
% 4.01/1.70  tff('#skF_3', type, '#skF_3': $i).
% 4.01/1.70  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.01/1.70  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.01/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.01/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.01/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.01/1.70  tff('#skF_4', type, '#skF_4': $i).
% 4.01/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.70  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.01/1.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.01/1.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.01/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.01/1.70  
% 4.01/1.72  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.01/1.72  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 4.01/1.72  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.01/1.72  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.01/1.72  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.01/1.72  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.01/1.72  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.01/1.72  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.01/1.72  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 4.01/1.72  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.01/1.72  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.01/1.72  tff(c_22, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.01/1.72  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.01/1.72  tff(c_551, plain, (![B_126, A_127]: (v1_relat_1(B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(A_127)) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.01/1.72  tff(c_554, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_551])).
% 4.01/1.72  tff(c_557, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_554])).
% 4.01/1.72  tff(c_576, plain, (![C_133, B_134, A_135]: (v5_relat_1(C_133, B_134) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_135, B_134))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.01/1.72  tff(c_580, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_576])).
% 4.01/1.72  tff(c_20, plain, (![B_13, A_12]: (r1_tarski(k2_relat_1(B_13), A_12) | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.01/1.72  tff(c_52, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.01/1.72  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.01/1.72  tff(c_586, plain, (![C_139, B_140, A_141]: (r2_hidden(C_139, B_140) | ~r2_hidden(C_139, A_141) | ~r1_tarski(A_141, B_140))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.01/1.72  tff(c_602, plain, (![A_146, B_147, B_148]: (r2_hidden('#skF_1'(A_146, B_147), B_148) | ~r1_tarski(A_146, B_148) | r1_tarski(A_146, B_147))), inference(resolution, [status(thm)], [c_6, c_586])).
% 4.01/1.72  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.01/1.72  tff(c_639, plain, (![A_158, B_159, B_160, B_161]: (r2_hidden('#skF_1'(A_158, B_159), B_160) | ~r1_tarski(B_161, B_160) | ~r1_tarski(A_158, B_161) | r1_tarski(A_158, B_159))), inference(resolution, [status(thm)], [c_602, c_2])).
% 4.01/1.72  tff(c_676, plain, (![A_167, B_168]: (r2_hidden('#skF_1'(A_167, B_168), '#skF_4') | ~r1_tarski(A_167, '#skF_3') | r1_tarski(A_167, B_168))), inference(resolution, [status(thm)], [c_52, c_639])).
% 4.01/1.72  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.01/1.72  tff(c_685, plain, (![A_169]: (~r1_tarski(A_169, '#skF_3') | r1_tarski(A_169, '#skF_4'))), inference(resolution, [status(thm)], [c_676, c_4])).
% 4.01/1.72  tff(c_698, plain, (![B_13]: (r1_tarski(k2_relat_1(B_13), '#skF_4') | ~v5_relat_1(B_13, '#skF_3') | ~v1_relat_1(B_13))), inference(resolution, [status(thm)], [c_20, c_685])).
% 4.01/1.72  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.01/1.72  tff(c_50, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.01/1.72  tff(c_65, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_50])).
% 4.01/1.72  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.01/1.72  tff(c_611, plain, (![A_149, B_150, C_151]: (k1_relset_1(A_149, B_150, C_151)=k1_relat_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.01/1.72  tff(c_615, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_611])).
% 4.01/1.72  tff(c_998, plain, (![B_219, A_220, C_221]: (k1_xboole_0=B_219 | k1_relset_1(A_220, B_219, C_221)=A_220 | ~v1_funct_2(C_221, A_220, B_219) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_220, B_219))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.01/1.72  tff(c_1004, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_998])).
% 4.01/1.72  tff(c_1008, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_615, c_1004])).
% 4.01/1.72  tff(c_1009, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_65, c_1008])).
% 4.01/1.72  tff(c_42, plain, (![B_26, A_25]: (m1_subset_1(B_26, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_26), A_25))) | ~r1_tarski(k2_relat_1(B_26), A_25) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.01/1.72  tff(c_1029, plain, (![A_25]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_25))) | ~r1_tarski(k2_relat_1('#skF_5'), A_25) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1009, c_42])).
% 4.01/1.72  tff(c_1120, plain, (![A_226]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_226))) | ~r1_tarski(k2_relat_1('#skF_5'), A_226))), inference(demodulation, [status(thm), theory('equality')], [c_557, c_58, c_1029])).
% 4.01/1.72  tff(c_48, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.01/1.72  tff(c_60, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_48])).
% 4.01/1.72  tff(c_66, plain, (~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 4.01/1.72  tff(c_67, plain, (![B_31, A_32]: (v1_relat_1(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(A_32)) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.01/1.72  tff(c_70, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_67])).
% 4.01/1.72  tff(c_73, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_70])).
% 4.01/1.72  tff(c_119, plain, (![C_43, B_44, A_45]: (v5_relat_1(C_43, B_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_45, B_44))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.01/1.72  tff(c_123, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_119])).
% 4.01/1.72  tff(c_124, plain, (![C_46, B_47, A_48]: (r2_hidden(C_46, B_47) | ~r2_hidden(C_46, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.01/1.72  tff(c_144, plain, (![A_55, B_56, B_57]: (r2_hidden('#skF_1'(A_55, B_56), B_57) | ~r1_tarski(A_55, B_57) | r1_tarski(A_55, B_56))), inference(resolution, [status(thm)], [c_6, c_124])).
% 4.01/1.72  tff(c_183, plain, (![A_70, B_71, B_72, B_73]: (r2_hidden('#skF_1'(A_70, B_71), B_72) | ~r1_tarski(B_73, B_72) | ~r1_tarski(A_70, B_73) | r1_tarski(A_70, B_71))), inference(resolution, [status(thm)], [c_144, c_2])).
% 4.01/1.72  tff(c_220, plain, (![A_79, B_80]: (r2_hidden('#skF_1'(A_79, B_80), '#skF_4') | ~r1_tarski(A_79, '#skF_3') | r1_tarski(A_79, B_80))), inference(resolution, [status(thm)], [c_52, c_183])).
% 4.01/1.72  tff(c_229, plain, (![A_81]: (~r1_tarski(A_81, '#skF_3') | r1_tarski(A_81, '#skF_4'))), inference(resolution, [status(thm)], [c_220, c_4])).
% 4.01/1.72  tff(c_242, plain, (![B_13]: (r1_tarski(k2_relat_1(B_13), '#skF_4') | ~v5_relat_1(B_13, '#skF_3') | ~v1_relat_1(B_13))), inference(resolution, [status(thm)], [c_20, c_229])).
% 4.01/1.72  tff(c_154, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.01/1.72  tff(c_158, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_154])).
% 4.01/1.72  tff(c_450, plain, (![B_117, A_118, C_119]: (k1_xboole_0=B_117 | k1_relset_1(A_118, B_117, C_119)=A_118 | ~v1_funct_2(C_119, A_118, B_117) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.01/1.72  tff(c_456, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_450])).
% 4.01/1.72  tff(c_460, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_158, c_456])).
% 4.01/1.72  tff(c_461, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_65, c_460])).
% 4.01/1.72  tff(c_44, plain, (![B_26, A_25]: (v1_funct_2(B_26, k1_relat_1(B_26), A_25) | ~r1_tarski(k2_relat_1(B_26), A_25) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.01/1.72  tff(c_478, plain, (![A_25]: (v1_funct_2('#skF_5', '#skF_2', A_25) | ~r1_tarski(k2_relat_1('#skF_5'), A_25) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_461, c_44])).
% 4.01/1.72  tff(c_500, plain, (![A_120]: (v1_funct_2('#skF_5', '#skF_2', A_120) | ~r1_tarski(k2_relat_1('#skF_5'), A_120))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_58, c_478])).
% 4.01/1.72  tff(c_504, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_242, c_500])).
% 4.01/1.72  tff(c_519, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_123, c_504])).
% 4.01/1.72  tff(c_521, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_519])).
% 4.01/1.72  tff(c_522, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_60])).
% 4.01/1.72  tff(c_1157, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_1120, c_522])).
% 4.01/1.72  tff(c_1160, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_698, c_1157])).
% 4.01/1.72  tff(c_1170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_557, c_580, c_1160])).
% 4.01/1.72  tff(c_1172, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_50])).
% 4.01/1.72  tff(c_1171, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_50])).
% 4.01/1.72  tff(c_1178, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1172, c_1171])).
% 4.01/1.72  tff(c_1183, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1178, c_54])).
% 4.01/1.72  tff(c_1192, plain, (![B_228, A_229]: (v1_relat_1(B_228) | ~m1_subset_1(B_228, k1_zfmisc_1(A_229)) | ~v1_relat_1(A_229))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.01/1.72  tff(c_1195, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_1183, c_1192])).
% 4.01/1.72  tff(c_1198, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1195])).
% 4.01/1.72  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.01/1.72  tff(c_1173, plain, (![A_8]: (r1_tarski('#skF_2', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_1171, c_14])).
% 4.01/1.72  tff(c_1189, plain, (![A_8]: (r1_tarski('#skF_3', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_1178, c_1173])).
% 4.01/1.72  tff(c_1594, plain, (![C_304, B_305, A_306]: (v5_relat_1(C_304, B_305) | ~m1_subset_1(C_304, k1_zfmisc_1(k2_zfmisc_1(A_306, B_305))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.01/1.72  tff(c_1598, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_1183, c_1594])).
% 4.01/1.72  tff(c_1568, plain, (![B_295, A_296]: (r1_tarski(k2_relat_1(B_295), A_296) | ~v5_relat_1(B_295, A_296) | ~v1_relat_1(B_295))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.01/1.72  tff(c_1545, plain, (![B_292, A_293]: (B_292=A_293 | ~r1_tarski(B_292, A_293) | ~r1_tarski(A_293, B_292))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.01/1.72  tff(c_1550, plain, (![A_8]: (A_8='#skF_3' | ~r1_tarski(A_8, '#skF_3'))), inference(resolution, [status(thm)], [c_1189, c_1545])).
% 4.01/1.72  tff(c_1575, plain, (![B_295]: (k2_relat_1(B_295)='#skF_3' | ~v5_relat_1(B_295, '#skF_3') | ~v1_relat_1(B_295))), inference(resolution, [status(thm)], [c_1568, c_1550])).
% 4.01/1.72  tff(c_1601, plain, (k2_relat_1('#skF_5')='#skF_3' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1598, c_1575])).
% 4.01/1.72  tff(c_1604, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1198, c_1601])).
% 4.01/1.72  tff(c_1184, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1178, c_56])).
% 4.01/1.72  tff(c_1646, plain, (![A_314, B_315, C_316]: (k1_relset_1(A_314, B_315, C_316)=k1_relat_1(C_316) | ~m1_subset_1(C_316, k1_zfmisc_1(k2_zfmisc_1(A_314, B_315))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.01/1.72  tff(c_1650, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1183, c_1646])).
% 4.01/1.72  tff(c_38, plain, (![B_23, C_24]: (k1_relset_1(k1_xboole_0, B_23, C_24)=k1_xboole_0 | ~v1_funct_2(C_24, k1_xboole_0, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_23))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.01/1.72  tff(c_1805, plain, (![B_342, C_343]: (k1_relset_1('#skF_3', B_342, C_343)='#skF_3' | ~v1_funct_2(C_343, '#skF_3', B_342) | ~m1_subset_1(C_343, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_342))))), inference(demodulation, [status(thm), theory('equality')], [c_1172, c_1172, c_1172, c_1172, c_38])).
% 4.01/1.72  tff(c_1808, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1183, c_1805])).
% 4.01/1.72  tff(c_1811, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1184, c_1650, c_1808])).
% 4.01/1.72  tff(c_1821, plain, (![A_25]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_25))) | ~r1_tarski(k2_relat_1('#skF_5'), A_25) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1811, c_42])).
% 4.01/1.72  tff(c_1830, plain, (![A_25]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_25))))), inference(demodulation, [status(thm), theory('equality')], [c_1198, c_58, c_1189, c_1604, c_1821])).
% 4.01/1.72  tff(c_1232, plain, (![C_237, B_238, A_239]: (v5_relat_1(C_237, B_238) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_239, B_238))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.01/1.72  tff(c_1236, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_1183, c_1232])).
% 4.01/1.72  tff(c_1237, plain, (![B_240, A_241]: (r1_tarski(k2_relat_1(B_240), A_241) | ~v5_relat_1(B_240, A_241) | ~v1_relat_1(B_240))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.01/1.72  tff(c_1209, plain, (![B_234, A_235]: (B_234=A_235 | ~r1_tarski(B_234, A_235) | ~r1_tarski(A_235, B_234))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.01/1.72  tff(c_1214, plain, (![A_8]: (A_8='#skF_3' | ~r1_tarski(A_8, '#skF_3'))), inference(resolution, [status(thm)], [c_1189, c_1209])).
% 4.01/1.72  tff(c_1246, plain, (![B_242]: (k2_relat_1(B_242)='#skF_3' | ~v5_relat_1(B_242, '#skF_3') | ~v1_relat_1(B_242))), inference(resolution, [status(thm)], [c_1237, c_1214])).
% 4.01/1.72  tff(c_1249, plain, (k2_relat_1('#skF_5')='#skF_3' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1236, c_1246])).
% 4.01/1.72  tff(c_1252, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1198, c_1249])).
% 4.01/1.72  tff(c_1312, plain, (![A_257, B_258, C_259]: (k1_relset_1(A_257, B_258, C_259)=k1_relat_1(C_259) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.01/1.72  tff(c_1316, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1183, c_1312])).
% 4.01/1.72  tff(c_1510, plain, (![B_290, C_291]: (k1_relset_1('#skF_3', B_290, C_291)='#skF_3' | ~v1_funct_2(C_291, '#skF_3', B_290) | ~m1_subset_1(C_291, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_290))))), inference(demodulation, [status(thm), theory('equality')], [c_1172, c_1172, c_1172, c_1172, c_38])).
% 4.01/1.72  tff(c_1513, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1183, c_1510])).
% 4.01/1.72  tff(c_1516, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1184, c_1316, c_1513])).
% 4.01/1.72  tff(c_1529, plain, (![A_25]: (v1_funct_2('#skF_5', '#skF_3', A_25) | ~r1_tarski(k2_relat_1('#skF_5'), A_25) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1516, c_44])).
% 4.01/1.72  tff(c_1537, plain, (![A_25]: (v1_funct_2('#skF_5', '#skF_3', A_25))), inference(demodulation, [status(thm), theory('equality')], [c_1198, c_58, c_1189, c_1252, c_1529])).
% 4.01/1.72  tff(c_1207, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1178, c_1178, c_60])).
% 4.01/1.72  tff(c_1208, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_1207])).
% 4.01/1.72  tff(c_1542, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1537, c_1208])).
% 4.01/1.72  tff(c_1543, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_1207])).
% 4.01/1.72  tff(c_1844, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1830, c_1543])).
% 4.01/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.72  
% 4.01/1.72  Inference rules
% 4.01/1.72  ----------------------
% 4.01/1.72  #Ref     : 0
% 4.01/1.72  #Sup     : 375
% 4.01/1.72  #Fact    : 0
% 4.01/1.72  #Define  : 0
% 4.01/1.72  #Split   : 8
% 4.01/1.72  #Chain   : 0
% 4.01/1.72  #Close   : 0
% 4.01/1.72  
% 4.01/1.72  Ordering : KBO
% 4.01/1.72  
% 4.01/1.72  Simplification rules
% 4.01/1.72  ----------------------
% 4.01/1.72  #Subsume      : 70
% 4.01/1.72  #Demod        : 221
% 4.01/1.72  #Tautology    : 147
% 4.01/1.72  #SimpNegUnit  : 5
% 4.01/1.72  #BackRed      : 12
% 4.01/1.72  
% 4.01/1.72  #Partial instantiations: 0
% 4.01/1.72  #Strategies tried      : 1
% 4.01/1.72  
% 4.01/1.72  Timing (in seconds)
% 4.01/1.72  ----------------------
% 4.01/1.72  Preprocessing        : 0.33
% 4.01/1.72  Parsing              : 0.17
% 4.01/1.72  CNF conversion       : 0.02
% 4.01/1.72  Main loop            : 0.60
% 4.01/1.72  Inferencing          : 0.23
% 4.01/1.72  Reduction            : 0.17
% 4.01/1.73  Demodulation         : 0.12
% 4.18/1.73  BG Simplification    : 0.02
% 4.18/1.73  Subsumption          : 0.12
% 4.18/1.73  Abstraction          : 0.02
% 4.18/1.73  MUC search           : 0.00
% 4.18/1.73  Cooper               : 0.00
% 4.18/1.73  Total                : 0.98
% 4.18/1.73  Index Insertion      : 0.00
% 4.18/1.73  Index Deletion       : 0.00
% 4.18/1.73  Index Matching       : 0.00
% 4.18/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
