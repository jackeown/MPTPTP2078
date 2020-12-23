%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:19 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 237 expanded)
%              Number of leaves         :   39 (  98 expanded)
%              Depth                    :   13
%              Number of atoms          :  179 ( 578 expanded)
%              Number of equality atoms :   43 ( 115 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ! [C] :
            ~ ( r2_hidden(C,A)
              & ! [D] :
                  ~ ( r2_hidden(D,k1_relat_1(B))
                    & C = k1_funct_1(B,D) ) )
       => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_103,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_50,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_92,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_96,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_92])).

tff(c_145,plain,(
    ! [C_68,B_69,A_70] :
      ( v5_relat_1(C_68,B_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_149,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_145])).

tff(c_22,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_162,plain,(
    ! [C_73,B_74,A_75] :
      ( r2_hidden(C_73,B_74)
      | ~ r2_hidden(C_73,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_177,plain,(
    ! [A_79,B_80] :
      ( r2_hidden('#skF_1'(A_79),B_80)
      | ~ r1_tarski(A_79,B_80)
      | v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_4,c_162])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_185,plain,(
    ! [B_81,A_82] :
      ( ~ v1_xboole_0(B_81)
      | ~ r1_tarski(A_82,B_81)
      | v1_xboole_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_177,c_2])).

tff(c_353,plain,(
    ! [A_99,B_100] :
      ( ~ v1_xboole_0(A_99)
      | v1_xboole_0(k2_relat_1(B_100))
      | ~ v5_relat_1(B_100,A_99)
      | ~ v1_relat_1(B_100) ) ),
    inference(resolution,[status(thm)],[c_22,c_185])).

tff(c_355,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0(k2_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_149,c_353])).

tff(c_360,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_355])).

tff(c_362,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_360])).

tff(c_426,plain,(
    ! [A_118,B_119,C_120] :
      ( k2_relset_1(A_118,B_119,C_120) = k2_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_430,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_426])).

tff(c_431,plain,(
    k2_relat_1('#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_50])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_3'(A_14,B_15),A_14)
      | r1_tarski(A_14,k2_relat_1(B_15))
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_60,plain,(
    ! [D_39] :
      ( r2_hidden('#skF_7'(D_39),'#skF_4')
      | ~ r2_hidden(D_39,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_170,plain,(
    ! [D_39,B_74] :
      ( r2_hidden('#skF_7'(D_39),B_74)
      | ~ r1_tarski('#skF_4',B_74)
      | ~ r2_hidden(D_39,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_162])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_363,plain,(
    ! [A_101,B_102,C_103] :
      ( k1_relset_1(A_101,B_102,C_103) = k1_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_367,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_363])).

tff(c_530,plain,(
    ! [B_155,A_156,C_157] :
      ( k1_xboole_0 = B_155
      | k1_relset_1(A_156,B_155,C_157) = A_156
      | ~ v1_funct_2(C_157,A_156,B_155)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_156,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_533,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_530])).

tff(c_536,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_367,c_533])).

tff(c_537,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_536])).

tff(c_58,plain,(
    ! [D_39] :
      ( k1_funct_1('#skF_6','#skF_7'(D_39)) = D_39
      | ~ r2_hidden(D_39,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_570,plain,(
    ! [B_165,D_166,A_167] :
      ( k1_funct_1(B_165,D_166) != '#skF_3'(A_167,B_165)
      | ~ r2_hidden(D_166,k1_relat_1(B_165))
      | r1_tarski(A_167,k2_relat_1(B_165))
      | ~ v1_funct_1(B_165)
      | ~ v1_relat_1(B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_572,plain,(
    ! [D_39,A_167] :
      ( D_39 != '#skF_3'(A_167,'#skF_6')
      | ~ r2_hidden('#skF_7'(D_39),k1_relat_1('#skF_6'))
      | r1_tarski(A_167,k2_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(D_39,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_570])).

tff(c_574,plain,(
    ! [D_39,A_167] :
      ( D_39 != '#skF_3'(A_167,'#skF_6')
      | ~ r2_hidden('#skF_7'(D_39),'#skF_4')
      | r1_tarski(A_167,k2_relat_1('#skF_6'))
      | ~ r2_hidden(D_39,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_56,c_537,c_572])).

tff(c_580,plain,(
    ! [A_170] :
      ( ~ r2_hidden('#skF_7'('#skF_3'(A_170,'#skF_6')),'#skF_4')
      | r1_tarski(A_170,k2_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_3'(A_170,'#skF_6'),'#skF_5') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_574])).

tff(c_583,plain,(
    ! [A_170] :
      ( r1_tarski(A_170,k2_relat_1('#skF_6'))
      | ~ r1_tarski('#skF_4','#skF_4')
      | ~ r2_hidden('#skF_3'(A_170,'#skF_6'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_170,c_580])).

tff(c_591,plain,(
    ! [A_171] :
      ( r1_tarski(A_171,k2_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_3'(A_171,'#skF_6'),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_583])).

tff(c_599,plain,
    ( r1_tarski('#skF_5',k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_591])).

tff(c_605,plain,(
    r1_tarski('#skF_5',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_56,c_599])).

tff(c_150,plain,(
    ! [B_71,A_72] :
      ( r1_tarski(k2_relat_1(B_71),A_72)
      | ~ v5_relat_1(B_71,A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_161,plain,(
    ! [B_71,A_72] :
      ( k2_relat_1(B_71) = A_72
      | ~ r1_tarski(A_72,k2_relat_1(B_71))
      | ~ v5_relat_1(B_71,A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(resolution,[status(thm)],[c_150,c_14])).

tff(c_618,plain,
    ( k2_relat_1('#skF_6') = '#skF_5'
    | ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_605,c_161])).

tff(c_643,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_149,c_618])).

tff(c_645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_431,c_643])).

tff(c_646,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_536])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_655,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_12])).

tff(c_657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_362,c_655])).

tff(c_658,plain,(
    v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_360])).

tff(c_659,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_360])).

tff(c_97,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_2'(A_54,B_55),A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_107,plain,(
    ! [A_54,B_55] :
      ( ~ v1_xboole_0(A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_97,c_2])).

tff(c_108,plain,(
    ! [A_56,B_57] :
      ( ~ v1_xboole_0(A_56)
      | r1_tarski(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_97,c_2])).

tff(c_112,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_108,c_14])).

tff(c_134,plain,(
    ! [B_63,A_64] :
      ( B_63 = A_64
      | ~ v1_xboole_0(B_63)
      | ~ v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_107,c_112])).

tff(c_137,plain,(
    ! [A_64] :
      ( k1_xboole_0 = A_64
      | ~ v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_12,c_134])).

tff(c_665,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_659,c_137])).

tff(c_694,plain,(
    ! [A_176] :
      ( A_176 = '#skF_5'
      | ~ v1_xboole_0(A_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_665,c_137])).

tff(c_701,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_658,c_694])).

tff(c_778,plain,(
    ! [A_180,B_181,C_182] :
      ( k2_relset_1(A_180,B_181,C_182) = k2_relat_1(C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_781,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_778])).

tff(c_783,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_701,c_781])).

tff(c_785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_783])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:15:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.53  
% 3.20/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.53  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 3.20/1.53  
% 3.20/1.53  %Foreground sorts:
% 3.20/1.53  
% 3.20/1.53  
% 3.20/1.53  %Background operators:
% 3.20/1.53  
% 3.20/1.53  
% 3.20/1.53  %Foreground operators:
% 3.20/1.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.20/1.53  tff('#skF_7', type, '#skF_7': $i > $i).
% 3.20/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.20/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.20/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.20/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.20/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.20/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.20/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.20/1.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.20/1.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.20/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.20/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.20/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.20/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.20/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.20/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.54  
% 3.20/1.55  tff(f_122, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 3.20/1.55  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.20/1.55  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.20/1.55  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.20/1.55  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.20/1.55  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.20/1.55  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.20/1.55  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, k1_relat_1(B)) & (C = k1_funct_1(B, D)))))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_funct_1)).
% 3.20/1.55  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.20/1.55  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.20/1.55  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.20/1.55  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.20/1.55  tff(c_50, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.20/1.55  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.20/1.55  tff(c_92, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.20/1.55  tff(c_96, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_92])).
% 3.20/1.55  tff(c_145, plain, (![C_68, B_69, A_70]: (v5_relat_1(C_68, B_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.20/1.55  tff(c_149, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_145])).
% 3.20/1.55  tff(c_22, plain, (![B_13, A_12]: (r1_tarski(k2_relat_1(B_13), A_12) | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.20/1.55  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.55  tff(c_162, plain, (![C_73, B_74, A_75]: (r2_hidden(C_73, B_74) | ~r2_hidden(C_73, A_75) | ~r1_tarski(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.20/1.55  tff(c_177, plain, (![A_79, B_80]: (r2_hidden('#skF_1'(A_79), B_80) | ~r1_tarski(A_79, B_80) | v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_4, c_162])).
% 3.20/1.55  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.55  tff(c_185, plain, (![B_81, A_82]: (~v1_xboole_0(B_81) | ~r1_tarski(A_82, B_81) | v1_xboole_0(A_82))), inference(resolution, [status(thm)], [c_177, c_2])).
% 3.20/1.55  tff(c_353, plain, (![A_99, B_100]: (~v1_xboole_0(A_99) | v1_xboole_0(k2_relat_1(B_100)) | ~v5_relat_1(B_100, A_99) | ~v1_relat_1(B_100))), inference(resolution, [status(thm)], [c_22, c_185])).
% 3.20/1.55  tff(c_355, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0(k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_149, c_353])).
% 3.20/1.55  tff(c_360, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0(k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_355])).
% 3.20/1.55  tff(c_362, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_360])).
% 3.20/1.55  tff(c_426, plain, (![A_118, B_119, C_120]: (k2_relset_1(A_118, B_119, C_120)=k2_relat_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.20/1.55  tff(c_430, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_426])).
% 3.20/1.55  tff(c_431, plain, (k2_relat_1('#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_430, c_50])).
% 3.20/1.55  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.20/1.55  tff(c_26, plain, (![A_14, B_15]: (r2_hidden('#skF_3'(A_14, B_15), A_14) | r1_tarski(A_14, k2_relat_1(B_15)) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.20/1.55  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.20/1.55  tff(c_60, plain, (![D_39]: (r2_hidden('#skF_7'(D_39), '#skF_4') | ~r2_hidden(D_39, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.20/1.55  tff(c_170, plain, (![D_39, B_74]: (r2_hidden('#skF_7'(D_39), B_74) | ~r1_tarski('#skF_4', B_74) | ~r2_hidden(D_39, '#skF_5'))), inference(resolution, [status(thm)], [c_60, c_162])).
% 3.20/1.55  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.20/1.55  tff(c_363, plain, (![A_101, B_102, C_103]: (k1_relset_1(A_101, B_102, C_103)=k1_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.20/1.55  tff(c_367, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_363])).
% 3.20/1.55  tff(c_530, plain, (![B_155, A_156, C_157]: (k1_xboole_0=B_155 | k1_relset_1(A_156, B_155, C_157)=A_156 | ~v1_funct_2(C_157, A_156, B_155) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_156, B_155))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.20/1.55  tff(c_533, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_530])).
% 3.20/1.55  tff(c_536, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_367, c_533])).
% 3.20/1.55  tff(c_537, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_536])).
% 3.20/1.55  tff(c_58, plain, (![D_39]: (k1_funct_1('#skF_6', '#skF_7'(D_39))=D_39 | ~r2_hidden(D_39, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.20/1.55  tff(c_570, plain, (![B_165, D_166, A_167]: (k1_funct_1(B_165, D_166)!='#skF_3'(A_167, B_165) | ~r2_hidden(D_166, k1_relat_1(B_165)) | r1_tarski(A_167, k2_relat_1(B_165)) | ~v1_funct_1(B_165) | ~v1_relat_1(B_165))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.20/1.55  tff(c_572, plain, (![D_39, A_167]: (D_39!='#skF_3'(A_167, '#skF_6') | ~r2_hidden('#skF_7'(D_39), k1_relat_1('#skF_6')) | r1_tarski(A_167, k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(D_39, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_570])).
% 3.20/1.55  tff(c_574, plain, (![D_39, A_167]: (D_39!='#skF_3'(A_167, '#skF_6') | ~r2_hidden('#skF_7'(D_39), '#skF_4') | r1_tarski(A_167, k2_relat_1('#skF_6')) | ~r2_hidden(D_39, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_56, c_537, c_572])).
% 3.20/1.55  tff(c_580, plain, (![A_170]: (~r2_hidden('#skF_7'('#skF_3'(A_170, '#skF_6')), '#skF_4') | r1_tarski(A_170, k2_relat_1('#skF_6')) | ~r2_hidden('#skF_3'(A_170, '#skF_6'), '#skF_5'))), inference(reflexivity, [status(thm), theory('equality')], [c_574])).
% 3.20/1.55  tff(c_583, plain, (![A_170]: (r1_tarski(A_170, k2_relat_1('#skF_6')) | ~r1_tarski('#skF_4', '#skF_4') | ~r2_hidden('#skF_3'(A_170, '#skF_6'), '#skF_5'))), inference(resolution, [status(thm)], [c_170, c_580])).
% 3.20/1.55  tff(c_591, plain, (![A_171]: (r1_tarski(A_171, k2_relat_1('#skF_6')) | ~r2_hidden('#skF_3'(A_171, '#skF_6'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_583])).
% 3.20/1.55  tff(c_599, plain, (r1_tarski('#skF_5', k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_591])).
% 3.20/1.55  tff(c_605, plain, (r1_tarski('#skF_5', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_56, c_599])).
% 3.20/1.55  tff(c_150, plain, (![B_71, A_72]: (r1_tarski(k2_relat_1(B_71), A_72) | ~v5_relat_1(B_71, A_72) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.20/1.55  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.20/1.55  tff(c_161, plain, (![B_71, A_72]: (k2_relat_1(B_71)=A_72 | ~r1_tarski(A_72, k2_relat_1(B_71)) | ~v5_relat_1(B_71, A_72) | ~v1_relat_1(B_71))), inference(resolution, [status(thm)], [c_150, c_14])).
% 3.20/1.55  tff(c_618, plain, (k2_relat_1('#skF_6')='#skF_5' | ~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_605, c_161])).
% 3.20/1.55  tff(c_643, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_149, c_618])).
% 3.20/1.55  tff(c_645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_431, c_643])).
% 3.20/1.55  tff(c_646, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_536])).
% 3.20/1.55  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.20/1.55  tff(c_655, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_646, c_12])).
% 3.20/1.55  tff(c_657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_362, c_655])).
% 3.20/1.55  tff(c_658, plain, (v1_xboole_0(k2_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_360])).
% 3.20/1.55  tff(c_659, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_360])).
% 3.20/1.55  tff(c_97, plain, (![A_54, B_55]: (r2_hidden('#skF_2'(A_54, B_55), A_54) | r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.20/1.55  tff(c_107, plain, (![A_54, B_55]: (~v1_xboole_0(A_54) | r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_97, c_2])).
% 3.20/1.55  tff(c_108, plain, (![A_56, B_57]: (~v1_xboole_0(A_56) | r1_tarski(A_56, B_57))), inference(resolution, [status(thm)], [c_97, c_2])).
% 3.20/1.55  tff(c_112, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_108, c_14])).
% 3.20/1.55  tff(c_134, plain, (![B_63, A_64]: (B_63=A_64 | ~v1_xboole_0(B_63) | ~v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_107, c_112])).
% 3.20/1.55  tff(c_137, plain, (![A_64]: (k1_xboole_0=A_64 | ~v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_12, c_134])).
% 3.20/1.55  tff(c_665, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_659, c_137])).
% 3.20/1.55  tff(c_694, plain, (![A_176]: (A_176='#skF_5' | ~v1_xboole_0(A_176))), inference(demodulation, [status(thm), theory('equality')], [c_665, c_137])).
% 3.20/1.55  tff(c_701, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_658, c_694])).
% 3.20/1.55  tff(c_778, plain, (![A_180, B_181, C_182]: (k2_relset_1(A_180, B_181, C_182)=k2_relat_1(C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.20/1.55  tff(c_781, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_778])).
% 3.20/1.55  tff(c_783, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_701, c_781])).
% 3.20/1.55  tff(c_785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_783])).
% 3.20/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.55  
% 3.20/1.55  Inference rules
% 3.20/1.55  ----------------------
% 3.20/1.55  #Ref     : 1
% 3.20/1.55  #Sup     : 157
% 3.20/1.55  #Fact    : 0
% 3.20/1.55  #Define  : 0
% 3.20/1.55  #Split   : 4
% 3.20/1.55  #Chain   : 0
% 3.20/1.55  #Close   : 0
% 3.20/1.55  
% 3.20/1.55  Ordering : KBO
% 3.20/1.55  
% 3.20/1.55  Simplification rules
% 3.20/1.55  ----------------------
% 3.20/1.55  #Subsume      : 34
% 3.20/1.55  #Demod        : 76
% 3.20/1.55  #Tautology    : 58
% 3.20/1.55  #SimpNegUnit  : 5
% 3.20/1.55  #BackRed      : 16
% 3.20/1.55  
% 3.20/1.55  #Partial instantiations: 0
% 3.20/1.55  #Strategies tried      : 1
% 3.20/1.55  
% 3.20/1.55  Timing (in seconds)
% 3.20/1.55  ----------------------
% 3.20/1.56  Preprocessing        : 0.36
% 3.20/1.56  Parsing              : 0.19
% 3.20/1.56  CNF conversion       : 0.02
% 3.20/1.56  Main loop            : 0.35
% 3.20/1.56  Inferencing          : 0.13
% 3.20/1.56  Reduction            : 0.10
% 3.20/1.56  Demodulation         : 0.07
% 3.20/1.56  BG Simplification    : 0.02
% 3.20/1.56  Subsumption          : 0.08
% 3.20/1.56  Abstraction          : 0.02
% 3.20/1.56  MUC search           : 0.00
% 3.20/1.56  Cooper               : 0.00
% 3.20/1.56  Total                : 0.75
% 3.20/1.56  Index Insertion      : 0.00
% 3.20/1.56  Index Deletion       : 0.00
% 3.20/1.56  Index Matching       : 0.00
% 3.20/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
