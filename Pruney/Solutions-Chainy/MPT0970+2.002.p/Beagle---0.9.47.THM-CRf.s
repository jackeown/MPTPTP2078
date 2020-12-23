%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:18 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 191 expanded)
%              Number of leaves         :   38 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  150 ( 472 expanded)
%              Number of equality atoms :   36 ( 109 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_6

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_95,axiom,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_48,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_82,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_86,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_82])).

tff(c_120,plain,(
    ! [C_55,B_56,A_57] :
      ( v5_relat_1(C_55,B_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_124,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_120])).

tff(c_22,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_364,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_relset_1(A_96,B_97,C_98) = k2_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_368,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_364])).

tff(c_369,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_48])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_145,plain,(
    ! [B_64,A_65] :
      ( r1_tarski(k2_relat_1(B_64),A_65)
      | ~ v5_relat_1(B_64,A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_95,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_2'(A_49,B_50),A_49)
      | r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [A_51,B_52] :
      ( ~ v1_xboole_0(A_51)
      | r1_tarski(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_95,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_109,plain,(
    ! [B_52,A_51] :
      ( B_52 = A_51
      | ~ r1_tarski(B_52,A_51)
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_106,c_14])).

tff(c_351,plain,(
    ! [B_94,A_95] :
      ( k2_relat_1(B_94) = A_95
      | ~ v1_xboole_0(A_95)
      | ~ v5_relat_1(B_94,A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(resolution,[status(thm)],[c_145,c_109])).

tff(c_357,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ v1_xboole_0('#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_124,c_351])).

tff(c_362,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_357])).

tff(c_363,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_362])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_426,plain,(
    ! [A_114,B_115,C_116] :
      ( k1_relset_1(A_114,B_115,C_116) = k1_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_430,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_426])).

tff(c_705,plain,(
    ! [B_167,A_168,C_169] :
      ( k1_xboole_0 = B_167
      | k1_relset_1(A_168,B_167,C_169) = A_168
      | ~ v1_funct_2(C_169,A_168,B_167)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_168,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_708,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_705])).

tff(c_711,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_430,c_708])).

tff(c_718,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_711])).

tff(c_58,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_6'(D_34),'#skF_3')
      | ~ r2_hidden(D_34,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_135,plain,(
    ! [C_61,B_62,A_63] :
      ( r2_hidden(C_61,B_62)
      | ~ r2_hidden(C_61,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_143,plain,(
    ! [D_34,B_62] :
      ( r2_hidden('#skF_6'(D_34),B_62)
      | ~ r1_tarski('#skF_3',B_62)
      | ~ r2_hidden(D_34,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_135])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_56,plain,(
    ! [D_34] :
      ( k1_funct_1('#skF_5','#skF_6'(D_34)) = D_34
      | ~ r2_hidden(D_34,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_431,plain,(
    ! [B_117,A_118] :
      ( r2_hidden(k1_funct_1(B_117,A_118),k2_relat_1(B_117))
      | ~ r2_hidden(A_118,k1_relat_1(B_117))
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_439,plain,(
    ! [D_34] :
      ( r2_hidden(D_34,k2_relat_1('#skF_5'))
      | ~ r2_hidden('#skF_6'(D_34),k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(D_34,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_431])).

tff(c_475,plain,(
    ! [D_122] :
      ( r2_hidden(D_122,k2_relat_1('#skF_5'))
      | ~ r2_hidden('#skF_6'(D_122),k1_relat_1('#skF_5'))
      | ~ r2_hidden(D_122,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_54,c_439])).

tff(c_480,plain,(
    ! [D_34] :
      ( r2_hidden(D_34,k2_relat_1('#skF_5'))
      | ~ r1_tarski('#skF_3',k1_relat_1('#skF_5'))
      | ~ r2_hidden(D_34,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_143,c_475])).

tff(c_499,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_480])).

tff(c_719,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_499])).

tff(c_724,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_719])).

tff(c_725,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_711])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_735,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_725,c_12])).

tff(c_737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_735])).

tff(c_792,plain,(
    ! [D_176] :
      ( r2_hidden(D_176,k2_relat_1('#skF_5'))
      | ~ r2_hidden(D_176,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_480])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_917,plain,(
    ! [A_187] :
      ( r1_tarski(A_187,k2_relat_1('#skF_5'))
      | ~ r2_hidden('#skF_2'(A_187,k2_relat_1('#skF_5')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_792,c_8])).

tff(c_927,plain,(
    r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_10,c_917])).

tff(c_939,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_927,c_14])).

tff(c_948,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_939])).

tff(c_951,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_948])).

tff(c_958,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_124,c_951])).

tff(c_959,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_362])).

tff(c_961,plain,(
    ! [A_188,B_189,C_190] :
      ( k2_relset_1(A_188,B_189,C_190) = k2_relat_1(C_190)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_965,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_961])).

tff(c_1003,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_959,c_965])).

tff(c_1004,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1003])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:30:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.46  
% 2.89/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.46  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_6
% 2.89/1.46  
% 2.89/1.46  %Foreground sorts:
% 2.89/1.46  
% 2.89/1.46  
% 2.89/1.46  %Background operators:
% 2.89/1.46  
% 2.89/1.46  
% 2.89/1.46  %Foreground operators:
% 2.89/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.89/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.89/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.89/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.89/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.89/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.89/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.89/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.89/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.89/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.89/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.89/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.89/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.89/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.89/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.89/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.89/1.46  tff('#skF_6', type, '#skF_6': $i > $i).
% 2.89/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.46  
% 3.28/1.48  tff(f_114, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 3.28/1.48  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.28/1.48  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.28/1.48  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.28/1.48  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.28/1.48  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.28/1.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.28/1.48  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.28/1.48  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.28/1.48  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.28/1.48  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 3.28/1.48  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.28/1.48  tff(c_48, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.28/1.48  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.28/1.48  tff(c_82, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.28/1.48  tff(c_86, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_82])).
% 3.28/1.48  tff(c_120, plain, (![C_55, B_56, A_57]: (v5_relat_1(C_55, B_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.28/1.48  tff(c_124, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_120])).
% 3.28/1.48  tff(c_22, plain, (![B_13, A_12]: (r1_tarski(k2_relat_1(B_13), A_12) | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.28/1.48  tff(c_364, plain, (![A_96, B_97, C_98]: (k2_relset_1(A_96, B_97, C_98)=k2_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.28/1.48  tff(c_368, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_364])).
% 3.28/1.48  tff(c_369, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_368, c_48])).
% 3.28/1.48  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.28/1.48  tff(c_145, plain, (![B_64, A_65]: (r1_tarski(k2_relat_1(B_64), A_65) | ~v5_relat_1(B_64, A_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.28/1.48  tff(c_95, plain, (![A_49, B_50]: (r2_hidden('#skF_2'(A_49, B_50), A_49) | r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.28/1.48  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.28/1.48  tff(c_106, plain, (![A_51, B_52]: (~v1_xboole_0(A_51) | r1_tarski(A_51, B_52))), inference(resolution, [status(thm)], [c_95, c_2])).
% 3.28/1.48  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.28/1.48  tff(c_109, plain, (![B_52, A_51]: (B_52=A_51 | ~r1_tarski(B_52, A_51) | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_106, c_14])).
% 3.28/1.48  tff(c_351, plain, (![B_94, A_95]: (k2_relat_1(B_94)=A_95 | ~v1_xboole_0(A_95) | ~v5_relat_1(B_94, A_95) | ~v1_relat_1(B_94))), inference(resolution, [status(thm)], [c_145, c_109])).
% 3.28/1.48  tff(c_357, plain, (k2_relat_1('#skF_5')='#skF_4' | ~v1_xboole_0('#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_124, c_351])).
% 3.28/1.48  tff(c_362, plain, (k2_relat_1('#skF_5')='#skF_4' | ~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_357])).
% 3.28/1.48  tff(c_363, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_362])).
% 3.28/1.48  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.28/1.48  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.28/1.48  tff(c_426, plain, (![A_114, B_115, C_116]: (k1_relset_1(A_114, B_115, C_116)=k1_relat_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.28/1.48  tff(c_430, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_426])).
% 3.28/1.48  tff(c_705, plain, (![B_167, A_168, C_169]: (k1_xboole_0=B_167 | k1_relset_1(A_168, B_167, C_169)=A_168 | ~v1_funct_2(C_169, A_168, B_167) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_168, B_167))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.28/1.48  tff(c_708, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_705])).
% 3.28/1.48  tff(c_711, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_430, c_708])).
% 3.28/1.48  tff(c_718, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_711])).
% 3.28/1.48  tff(c_58, plain, (![D_34]: (r2_hidden('#skF_6'(D_34), '#skF_3') | ~r2_hidden(D_34, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.28/1.48  tff(c_135, plain, (![C_61, B_62, A_63]: (r2_hidden(C_61, B_62) | ~r2_hidden(C_61, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.28/1.48  tff(c_143, plain, (![D_34, B_62]: (r2_hidden('#skF_6'(D_34), B_62) | ~r1_tarski('#skF_3', B_62) | ~r2_hidden(D_34, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_135])).
% 3.28/1.48  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.28/1.48  tff(c_56, plain, (![D_34]: (k1_funct_1('#skF_5', '#skF_6'(D_34))=D_34 | ~r2_hidden(D_34, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.28/1.48  tff(c_431, plain, (![B_117, A_118]: (r2_hidden(k1_funct_1(B_117, A_118), k2_relat_1(B_117)) | ~r2_hidden(A_118, k1_relat_1(B_117)) | ~v1_funct_1(B_117) | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.28/1.48  tff(c_439, plain, (![D_34]: (r2_hidden(D_34, k2_relat_1('#skF_5')) | ~r2_hidden('#skF_6'(D_34), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden(D_34, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_431])).
% 3.28/1.48  tff(c_475, plain, (![D_122]: (r2_hidden(D_122, k2_relat_1('#skF_5')) | ~r2_hidden('#skF_6'(D_122), k1_relat_1('#skF_5')) | ~r2_hidden(D_122, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_54, c_439])).
% 3.28/1.48  tff(c_480, plain, (![D_34]: (r2_hidden(D_34, k2_relat_1('#skF_5')) | ~r1_tarski('#skF_3', k1_relat_1('#skF_5')) | ~r2_hidden(D_34, '#skF_4'))), inference(resolution, [status(thm)], [c_143, c_475])).
% 3.28/1.48  tff(c_499, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_480])).
% 3.28/1.48  tff(c_719, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_718, c_499])).
% 3.28/1.48  tff(c_724, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_719])).
% 3.28/1.48  tff(c_725, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_711])).
% 3.28/1.48  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.28/1.48  tff(c_735, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_725, c_12])).
% 3.28/1.48  tff(c_737, plain, $false, inference(negUnitSimplification, [status(thm)], [c_363, c_735])).
% 3.28/1.48  tff(c_792, plain, (![D_176]: (r2_hidden(D_176, k2_relat_1('#skF_5')) | ~r2_hidden(D_176, '#skF_4'))), inference(splitRight, [status(thm)], [c_480])).
% 3.28/1.48  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.28/1.48  tff(c_917, plain, (![A_187]: (r1_tarski(A_187, k2_relat_1('#skF_5')) | ~r2_hidden('#skF_2'(A_187, k2_relat_1('#skF_5')), '#skF_4'))), inference(resolution, [status(thm)], [c_792, c_8])).
% 3.28/1.48  tff(c_927, plain, (r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_10, c_917])).
% 3.28/1.48  tff(c_939, plain, (k2_relat_1('#skF_5')='#skF_4' | ~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_927, c_14])).
% 3.28/1.48  tff(c_948, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_369, c_939])).
% 3.28/1.48  tff(c_951, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_948])).
% 3.28/1.48  tff(c_958, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_124, c_951])).
% 3.28/1.48  tff(c_959, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_362])).
% 3.28/1.48  tff(c_961, plain, (![A_188, B_189, C_190]: (k2_relset_1(A_188, B_189, C_190)=k2_relat_1(C_190) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.28/1.48  tff(c_965, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_961])).
% 3.28/1.48  tff(c_1003, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_959, c_965])).
% 3.28/1.48  tff(c_1004, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1003])).
% 3.28/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.48  
% 3.28/1.48  Inference rules
% 3.28/1.48  ----------------------
% 3.28/1.48  #Ref     : 0
% 3.28/1.48  #Sup     : 197
% 3.28/1.48  #Fact    : 0
% 3.28/1.48  #Define  : 0
% 3.28/1.48  #Split   : 10
% 3.28/1.48  #Chain   : 0
% 3.28/1.48  #Close   : 0
% 3.28/1.48  
% 3.28/1.48  Ordering : KBO
% 3.28/1.48  
% 3.28/1.48  Simplification rules
% 3.28/1.48  ----------------------
% 3.28/1.48  #Subsume      : 68
% 3.28/1.48  #Demod        : 69
% 3.28/1.48  #Tautology    : 44
% 3.28/1.48  #SimpNegUnit  : 10
% 3.28/1.48  #BackRed      : 18
% 3.28/1.48  
% 3.28/1.48  #Partial instantiations: 0
% 3.28/1.48  #Strategies tried      : 1
% 3.28/1.48  
% 3.28/1.48  Timing (in seconds)
% 3.28/1.48  ----------------------
% 3.28/1.49  Preprocessing        : 0.32
% 3.28/1.49  Parsing              : 0.16
% 3.28/1.49  CNF conversion       : 0.02
% 3.38/1.49  Main loop            : 0.41
% 3.38/1.49  Inferencing          : 0.15
% 3.38/1.49  Reduction            : 0.11
% 3.38/1.49  Demodulation         : 0.07
% 3.38/1.49  BG Simplification    : 0.02
% 3.38/1.49  Subsumption          : 0.10
% 3.38/1.49  Abstraction          : 0.02
% 3.38/1.49  MUC search           : 0.00
% 3.38/1.49  Cooper               : 0.00
% 3.38/1.49  Total                : 0.77
% 3.38/1.49  Index Insertion      : 0.00
% 3.38/1.49  Index Deletion       : 0.00
% 3.38/1.49  Index Matching       : 0.00
% 3.38/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
