%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:24 EST 2020

% Result     : Theorem 21.02s
% Output     : CNFRefutation 21.23s
% Verified   : 
% Statistics : Number of formulae       :  189 (2460 expanded)
%              Number of leaves         :   39 ( 862 expanded)
%              Depth                    :   16
%              Number of atoms          :  366 (7968 expanded)
%              Number of equality atoms :  109 (3070 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
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

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
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

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_144,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_148,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_144])).

tff(c_52,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_149,plain,(
    k2_relat_1('#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_52])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [D_39] :
      ( r2_hidden('#skF_7'(D_39),'#skF_4')
      | ~ r2_hidden(D_39,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_56,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_167,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_171,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_167])).

tff(c_84395,plain,(
    ! [B_6026,A_6027,C_6028] :
      ( k1_xboole_0 = B_6026
      | k1_relset_1(A_6027,B_6026,C_6028) = A_6027
      | ~ v1_funct_2(C_6028,A_6027,B_6026)
      | ~ m1_subset_1(C_6028,k1_zfmisc_1(k2_zfmisc_1(A_6027,B_6026))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_84398,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_84395])).

tff(c_84401,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_171,c_84398])).

tff(c_84402,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_84401])).

tff(c_89,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_93,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_89])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_60,plain,(
    ! [D_39] :
      ( k1_funct_1('#skF_6','#skF_7'(D_39)) = D_39
      | ~ r2_hidden(D_39,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_333,plain,(
    ! [B_118,A_119] :
      ( r2_hidden(k1_funct_1(B_118,A_119),k2_relat_1(B_118))
      | ~ r2_hidden(A_119,k1_relat_1(B_118))
      | ~ v1_funct_1(B_118)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_341,plain,(
    ! [D_39] :
      ( r2_hidden(D_39,k2_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_7'(D_39),k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(D_39,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_333])).

tff(c_345,plain,(
    ! [D_39] :
      ( r2_hidden(D_39,k2_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_7'(D_39),k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_39,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_58,c_341])).

tff(c_84501,plain,(
    ! [D_6036] :
      ( r2_hidden(D_6036,k2_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_7'(D_6036),'#skF_4')
      | ~ r2_hidden(D_6036,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84402,c_345])).

tff(c_84510,plain,(
    ! [D_39] :
      ( r2_hidden(D_39,k2_relat_1('#skF_6'))
      | ~ r2_hidden(D_39,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_84501])).

tff(c_127,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_1'(A_71,B_72),B_72)
      | r2_hidden('#skF_2'(A_71,B_72),A_71)
      | B_72 = A_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [C_12,A_9,B_10] :
      ( r2_hidden(C_12,A_9)
      | ~ r2_hidden(C_12,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_84931,plain,(
    ! [A_6062,B_6063,A_6064] :
      ( r2_hidden('#skF_2'(A_6062,B_6063),A_6064)
      | ~ m1_subset_1(A_6062,k1_zfmisc_1(A_6064))
      | r2_hidden('#skF_1'(A_6062,B_6063),B_6063)
      | B_6063 = A_6062 ) ),
    inference(resolution,[status(thm)],[c_127,c_18])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85039,plain,(
    ! [A_6065,A_6066] :
      ( ~ m1_subset_1(A_6065,k1_zfmisc_1(A_6066))
      | r2_hidden('#skF_1'(A_6065,A_6066),A_6066)
      | A_6066 = A_6065 ) ),
    inference(resolution,[status(thm)],[c_84931,c_4])).

tff(c_85345,plain,(
    ! [A_6090,A_6091,A_6092] :
      ( r2_hidden('#skF_1'(A_6090,A_6091),A_6092)
      | ~ m1_subset_1(A_6091,k1_zfmisc_1(A_6092))
      | ~ m1_subset_1(A_6090,k1_zfmisc_1(A_6091))
      | A_6091 = A_6090 ) ),
    inference(resolution,[status(thm)],[c_85039,c_18])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85600,plain,(
    ! [A_6120,A_6121] :
      ( ~ r2_hidden('#skF_2'(A_6120,A_6121),A_6121)
      | ~ m1_subset_1(A_6121,k1_zfmisc_1(A_6120))
      | ~ m1_subset_1(A_6120,k1_zfmisc_1(A_6121))
      | A_6121 = A_6120 ) ),
    inference(resolution,[status(thm)],[c_85345,c_2])).

tff(c_104148,plain,(
    ! [A_7374] :
      ( ~ m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1(A_7374))
      | ~ m1_subset_1(A_7374,k1_zfmisc_1(k2_relat_1('#skF_6')))
      | k2_relat_1('#skF_6') = A_7374
      | ~ r2_hidden('#skF_2'(A_7374,k2_relat_1('#skF_6')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_84510,c_85600])).

tff(c_104168,plain,
    ( ~ m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_relat_1('#skF_6')))
    | ~ r2_hidden('#skF_1'('#skF_5',k2_relat_1('#skF_6')),'#skF_5')
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6,c_104148])).

tff(c_104178,plain,
    ( ~ m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_relat_1('#skF_6')))
    | ~ r2_hidden('#skF_1'('#skF_5',k2_relat_1('#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_149,c_104168])).

tff(c_104233,plain,(
    ~ r2_hidden('#skF_1'('#skF_5',k2_relat_1('#skF_6')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_104178])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [A_19] :
      ( k9_relat_1(A_19,k1_relat_1(A_19)) = k2_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22716,plain,(
    ! [A_2136,B_2137,C_2138] :
      ( r2_hidden(k4_tarski('#skF_3'(A_2136,B_2137,C_2138),A_2136),C_2138)
      | ~ r2_hidden(A_2136,k9_relat_1(C_2138,B_2137))
      | ~ v1_relat_1(C_2138) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_94516,plain,(
    ! [A_6727,B_6728,C_6729,A_6730] :
      ( r2_hidden(k4_tarski('#skF_3'(A_6727,B_6728,C_6729),A_6727),A_6730)
      | ~ m1_subset_1(C_6729,k1_zfmisc_1(A_6730))
      | ~ r2_hidden(A_6727,k9_relat_1(C_6729,B_6728))
      | ~ v1_relat_1(C_6729) ) ),
    inference(resolution,[status(thm)],[c_22716,c_18])).

tff(c_14,plain,(
    ! [B_6,D_8,A_5,C_7] :
      ( r2_hidden(B_6,D_8)
      | ~ r2_hidden(k4_tarski(A_5,B_6),k2_zfmisc_1(C_7,D_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_112705,plain,(
    ! [B_7818,C_7816,A_7817,C_7819,D_7815] :
      ( r2_hidden(A_7817,D_7815)
      | ~ m1_subset_1(C_7816,k1_zfmisc_1(k2_zfmisc_1(C_7819,D_7815)))
      | ~ r2_hidden(A_7817,k9_relat_1(C_7816,B_7818))
      | ~ v1_relat_1(C_7816) ) ),
    inference(resolution,[status(thm)],[c_94516,c_14])).

tff(c_112707,plain,(
    ! [A_7817,B_7818] :
      ( r2_hidden(A_7817,'#skF_5')
      | ~ r2_hidden(A_7817,k9_relat_1('#skF_6',B_7818))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_112705])).

tff(c_112711,plain,(
    ! [A_7820,B_7821] :
      ( r2_hidden(A_7820,'#skF_5')
      | ~ r2_hidden(A_7820,k9_relat_1('#skF_6',B_7821)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_112707])).

tff(c_112851,plain,(
    ! [A_7820] :
      ( r2_hidden(A_7820,'#skF_5')
      | ~ r2_hidden(A_7820,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_112711])).

tff(c_112891,plain,(
    ! [A_7822] :
      ( r2_hidden(A_7822,'#skF_5')
      | ~ r2_hidden(A_7822,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_112851])).

tff(c_113048,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1,k2_relat_1('#skF_6')),'#skF_5')
      | r2_hidden('#skF_2'(A_1,k2_relat_1('#skF_6')),A_1)
      | k2_relat_1('#skF_6') = A_1 ) ),
    inference(resolution,[status(thm)],[c_8,c_112891])).

tff(c_84511,plain,(
    ! [D_6037] :
      ( r2_hidden(D_6037,k2_relat_1('#skF_6'))
      | ~ r2_hidden(D_6037,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_84501])).

tff(c_84537,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1,k2_relat_1('#skF_6')),k2_relat_1('#skF_6'))
      | k2_relat_1('#skF_6') = A_1
      | ~ r2_hidden('#skF_2'(A_1,k2_relat_1('#skF_6')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_84511,c_4])).

tff(c_116047,plain,(
    ! [A_7957] :
      ( r2_hidden('#skF_1'(A_7957,k2_relat_1('#skF_6')),'#skF_5')
      | k2_relat_1('#skF_6') = A_7957
      | ~ r2_hidden('#skF_2'(A_7957,k2_relat_1('#skF_6')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_84537,c_112891])).

tff(c_116055,plain,
    ( r2_hidden('#skF_1'('#skF_5',k2_relat_1('#skF_6')),'#skF_5')
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_113048,c_116047])).

tff(c_116091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_104233,c_149,c_104233,c_116055])).

tff(c_116093,plain,(
    r2_hidden('#skF_1'('#skF_5',k2_relat_1('#skF_6')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_104178])).

tff(c_116102,plain,
    ( ~ r2_hidden('#skF_2'('#skF_5',k2_relat_1('#skF_6')),k2_relat_1('#skF_6'))
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_116093,c_2])).

tff(c_116117,plain,(
    ~ r2_hidden('#skF_2'('#skF_5',k2_relat_1('#skF_6')),k2_relat_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_116102])).

tff(c_116134,plain,(
    ~ r2_hidden('#skF_2'('#skF_5',k2_relat_1('#skF_6')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_84510,c_116117])).

tff(c_116157,plain,
    ( ~ r2_hidden('#skF_1'('#skF_5',k2_relat_1('#skF_6')),'#skF_5')
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6,c_116134])).

tff(c_116167,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116093,c_116157])).

tff(c_116169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_116167])).

tff(c_116171,plain,(
    k1_relat_1('#skF_6') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_84401])).

tff(c_116170,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_84401])).

tff(c_42,plain,(
    ! [C_35,A_33] :
      ( k1_xboole_0 = C_35
      | ~ v1_funct_2(C_35,A_33,k1_xboole_0)
      | k1_xboole_0 = A_33
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_116527,plain,(
    ! [C_7985,A_7986] :
      ( C_7985 = '#skF_5'
      | ~ v1_funct_2(C_7985,A_7986,'#skF_5')
      | A_7986 = '#skF_5'
      | ~ m1_subset_1(C_7985,k1_zfmisc_1(k2_zfmisc_1(A_7986,'#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116170,c_116170,c_116170,c_116170,c_42])).

tff(c_116530,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_116527])).

tff(c_116533,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_116530])).

tff(c_116534,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_116533])).

tff(c_116559,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116534,c_56])).

tff(c_116558,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116534,c_54])).

tff(c_48,plain,(
    ! [B_34,C_35] :
      ( k1_relset_1(k1_xboole_0,B_34,C_35) = k1_xboole_0
      | ~ v1_funct_2(C_35,k1_xboole_0,B_34)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_116187,plain,(
    ! [B_34,C_35] :
      ( k1_relset_1('#skF_5',B_34,C_35) = '#skF_5'
      | ~ v1_funct_2(C_35,'#skF_5',B_34)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_34))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116170,c_116170,c_116170,c_116170,c_48])).

tff(c_116606,plain,(
    ! [B_34,C_35] :
      ( k1_relset_1('#skF_4',B_34,C_35) = '#skF_4'
      | ~ v1_funct_2(C_35,'#skF_4',B_34)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_34))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116534,c_116534,c_116534,c_116534,c_116187])).

tff(c_116645,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_116558,c_116606])).

tff(c_116657,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116559,c_116645])).

tff(c_116555,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116534,c_171])).

tff(c_116706,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116657,c_116555])).

tff(c_116707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116171,c_116706])).

tff(c_116708,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_116533])).

tff(c_116731,plain,(
    k2_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116708,c_149])).

tff(c_22829,plain,(
    ! [B_2144,A_2145,C_2146] :
      ( k1_xboole_0 = B_2144
      | k1_relset_1(A_2145,B_2144,C_2146) = A_2145
      | ~ v1_funct_2(C_2146,A_2145,B_2144)
      | ~ m1_subset_1(C_2146,k1_zfmisc_1(k2_zfmisc_1(A_2145,B_2144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_22832,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_22829])).

tff(c_22835,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_171,c_22832])).

tff(c_22836,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_22835])).

tff(c_22868,plain,(
    ! [D_2147] :
      ( r2_hidden(D_2147,k2_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_7'(D_2147),'#skF_4')
      | ~ r2_hidden(D_2147,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22836,c_345])).

tff(c_22877,plain,(
    ! [D_39] :
      ( r2_hidden(D_39,k2_relat_1('#skF_6'))
      | ~ r2_hidden(D_39,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_22868])).

tff(c_23624,plain,(
    ! [A_2213,B_2214,A_2215] :
      ( r2_hidden('#skF_2'(A_2213,B_2214),A_2215)
      | ~ m1_subset_1(A_2213,k1_zfmisc_1(A_2215))
      | r2_hidden('#skF_1'(A_2213,B_2214),B_2214)
      | B_2214 = A_2213 ) ),
    inference(resolution,[status(thm)],[c_127,c_18])).

tff(c_23747,plain,(
    ! [A_2216,A_2217] :
      ( ~ m1_subset_1(A_2216,k1_zfmisc_1(A_2217))
      | r2_hidden('#skF_1'(A_2216,A_2217),A_2217)
      | A_2217 = A_2216 ) ),
    inference(resolution,[status(thm)],[c_23624,c_4])).

tff(c_26357,plain,(
    ! [A_2452,A_2453,A_2454] :
      ( r2_hidden('#skF_1'(A_2452,A_2453),A_2454)
      | ~ m1_subset_1(A_2453,k1_zfmisc_1(A_2454))
      | ~ m1_subset_1(A_2452,k1_zfmisc_1(A_2453))
      | A_2453 = A_2452 ) ),
    inference(resolution,[status(thm)],[c_23747,c_18])).

tff(c_26433,plain,(
    ! [A_2462,A_2463] :
      ( ~ r2_hidden('#skF_2'(A_2462,A_2463),A_2463)
      | ~ m1_subset_1(A_2463,k1_zfmisc_1(A_2462))
      | ~ m1_subset_1(A_2462,k1_zfmisc_1(A_2463))
      | A_2463 = A_2462 ) ),
    inference(resolution,[status(thm)],[c_26357,c_2])).

tff(c_39073,plain,(
    ! [A_3406] :
      ( ~ m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1(A_3406))
      | ~ m1_subset_1(A_3406,k1_zfmisc_1(k2_relat_1('#skF_6')))
      | k2_relat_1('#skF_6') = A_3406
      | ~ r2_hidden('#skF_2'(A_3406,k2_relat_1('#skF_6')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22877,c_26433])).

tff(c_39093,plain,
    ( ~ m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_relat_1('#skF_6')))
    | ~ r2_hidden('#skF_1'('#skF_5',k2_relat_1('#skF_6')),'#skF_5')
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6,c_39073])).

tff(c_39103,plain,
    ( ~ m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_relat_1('#skF_6')))
    | ~ r2_hidden('#skF_1'('#skF_5',k2_relat_1('#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_149,c_39093])).

tff(c_39285,plain,(
    ~ r2_hidden('#skF_1'('#skF_5',k2_relat_1('#skF_6')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_39103])).

tff(c_28840,plain,(
    ! [A_2646,B_2647,C_2648,A_2649] :
      ( r2_hidden(k4_tarski('#skF_3'(A_2646,B_2647,C_2648),A_2646),A_2649)
      | ~ m1_subset_1(C_2648,k1_zfmisc_1(A_2649))
      | ~ r2_hidden(A_2646,k9_relat_1(C_2648,B_2647))
      | ~ v1_relat_1(C_2648) ) ),
    inference(resolution,[status(thm)],[c_22716,c_18])).

tff(c_46255,plain,(
    ! [C_3823,A_3821,C_3820,D_3819,B_3822] :
      ( r2_hidden(A_3821,D_3819)
      | ~ m1_subset_1(C_3823,k1_zfmisc_1(k2_zfmisc_1(C_3820,D_3819)))
      | ~ r2_hidden(A_3821,k9_relat_1(C_3823,B_3822))
      | ~ v1_relat_1(C_3823) ) ),
    inference(resolution,[status(thm)],[c_28840,c_14])).

tff(c_46257,plain,(
    ! [A_3821,B_3822] :
      ( r2_hidden(A_3821,'#skF_5')
      | ~ r2_hidden(A_3821,k9_relat_1('#skF_6',B_3822))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_46255])).

tff(c_46261,plain,(
    ! [A_3824,B_3825] :
      ( r2_hidden(A_3824,'#skF_5')
      | ~ r2_hidden(A_3824,k9_relat_1('#skF_6',B_3825)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_46257])).

tff(c_46401,plain,(
    ! [A_3824] :
      ( r2_hidden(A_3824,'#skF_5')
      | ~ r2_hidden(A_3824,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_46261])).

tff(c_46441,plain,(
    ! [A_3826] :
      ( r2_hidden(A_3826,'#skF_5')
      | ~ r2_hidden(A_3826,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_46401])).

tff(c_46598,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1,k2_relat_1('#skF_6')),'#skF_5')
      | r2_hidden('#skF_2'(A_1,k2_relat_1('#skF_6')),A_1)
      | k2_relat_1('#skF_6') = A_1 ) ),
    inference(resolution,[status(thm)],[c_8,c_46441])).

tff(c_22878,plain,(
    ! [D_2148] :
      ( r2_hidden(D_2148,k2_relat_1('#skF_6'))
      | ~ r2_hidden(D_2148,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_22868])).

tff(c_22896,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1,k2_relat_1('#skF_6')),k2_relat_1('#skF_6'))
      | k2_relat_1('#skF_6') = A_1
      | ~ r2_hidden('#skF_2'(A_1,k2_relat_1('#skF_6')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22878,c_4])).

tff(c_49573,plain,(
    ! [A_3961] :
      ( r2_hidden('#skF_1'(A_3961,k2_relat_1('#skF_6')),'#skF_5')
      | k2_relat_1('#skF_6') = A_3961
      | ~ r2_hidden('#skF_2'(A_3961,k2_relat_1('#skF_6')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22896,c_46441])).

tff(c_49577,plain,
    ( r2_hidden('#skF_1'('#skF_5',k2_relat_1('#skF_6')),'#skF_5')
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46598,c_49573])).

tff(c_49617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_39285,c_149,c_39285,c_49577])).

tff(c_49619,plain,(
    r2_hidden('#skF_1'('#skF_5',k2_relat_1('#skF_6')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_39103])).

tff(c_49628,plain,
    ( ~ r2_hidden('#skF_2'('#skF_5',k2_relat_1('#skF_6')),k2_relat_1('#skF_6'))
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_49619,c_2])).

tff(c_49643,plain,(
    ~ r2_hidden('#skF_2'('#skF_5',k2_relat_1('#skF_6')),k2_relat_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_49628])).

tff(c_49676,plain,(
    ~ r2_hidden('#skF_2'('#skF_5',k2_relat_1('#skF_6')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_22877,c_49643])).

tff(c_49690,plain,
    ( ~ r2_hidden('#skF_1'('#skF_5',k2_relat_1('#skF_6')),'#skF_5')
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6,c_49676])).

tff(c_49700,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49619,c_49690])).

tff(c_49702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_49700])).

tff(c_49704,plain,(
    k1_relat_1('#skF_6') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22835])).

tff(c_49703,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_22835])).

tff(c_50091,plain,(
    ! [C_4000,A_4001] :
      ( C_4000 = '#skF_5'
      | ~ v1_funct_2(C_4000,A_4001,'#skF_5')
      | A_4001 = '#skF_5'
      | ~ m1_subset_1(C_4000,k1_zfmisc_1(k2_zfmisc_1(A_4001,'#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49703,c_49703,c_49703,c_49703,c_42])).

tff(c_50094,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_50091])).

tff(c_50097,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50094])).

tff(c_50098,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_50097])).

tff(c_50127,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50098,c_56])).

tff(c_50123,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50098,c_171])).

tff(c_50126,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50098,c_54])).

tff(c_49718,plain,(
    ! [B_34,C_35] :
      ( k1_relset_1('#skF_5',B_34,C_35) = '#skF_5'
      | ~ v1_funct_2(C_35,'#skF_5',B_34)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_34))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49703,c_49703,c_49703,c_49703,c_48])).

tff(c_50538,plain,(
    ! [B_4037,C_4038] :
      ( k1_relset_1('#skF_4',B_4037,C_4038) = '#skF_4'
      | ~ v1_funct_2(C_4038,'#skF_4',B_4037)
      | ~ m1_subset_1(C_4038,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_4037))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50098,c_50098,c_50098,c_50098,c_49718])).

tff(c_50541,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_50126,c_50538])).

tff(c_50544,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50127,c_50123,c_50541])).

tff(c_50546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49704,c_50544])).

tff(c_50547,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50097])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_32,plain,(
    ! [B_23,A_22] :
      ( ~ r1_tarski(B_23,A_22)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_263,plain,(
    ! [A_101,B_102] :
      ( ~ r1_tarski(A_101,'#skF_2'(A_101,B_102))
      | r2_hidden('#skF_1'(A_101,B_102),B_102)
      | B_102 = A_101 ) ),
    inference(resolution,[status(thm)],[c_127,c_32])).

tff(c_267,plain,(
    ! [B_102] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_102),B_102)
      | k1_xboole_0 = B_102 ) ),
    inference(resolution,[status(thm)],[c_10,c_263])).

tff(c_204,plain,(
    ! [A_88,B_89,C_90] :
      ( r2_hidden('#skF_3'(A_88,B_89,C_90),B_89)
      | ~ r2_hidden(A_88,k9_relat_1(C_90,B_89))
      | ~ v1_relat_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_353,plain,(
    ! [B_121,A_122,C_123] :
      ( ~ r1_tarski(B_121,'#skF_3'(A_122,B_121,C_123))
      | ~ r2_hidden(A_122,k9_relat_1(C_123,B_121))
      | ~ v1_relat_1(C_123) ) ),
    inference(resolution,[status(thm)],[c_204,c_32])).

tff(c_358,plain,(
    ! [A_124,C_125] :
      ( ~ r2_hidden(A_124,k9_relat_1(C_125,k1_xboole_0))
      | ~ v1_relat_1(C_125) ) ),
    inference(resolution,[status(thm)],[c_10,c_353])).

tff(c_405,plain,(
    ! [C_128] :
      ( ~ v1_relat_1(C_128)
      | k9_relat_1(C_128,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_267,c_358])).

tff(c_409,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_93,c_405])).

tff(c_357,plain,(
    ! [A_122,C_123] :
      ( ~ r2_hidden(A_122,k9_relat_1(C_123,k1_xboole_0))
      | ~ v1_relat_1(C_123) ) ),
    inference(resolution,[status(thm)],[c_10,c_353])).

tff(c_413,plain,(
    ! [A_122] :
      ( ~ r2_hidden(A_122,k1_xboole_0)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_357])).

tff(c_417,plain,(
    ! [A_122] : ~ r2_hidden(A_122,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_413])).

tff(c_22743,plain,(
    ! [A_2136,B_2137] :
      ( ~ r2_hidden(A_2136,k9_relat_1(k1_xboole_0,B_2137))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22716,c_417])).

tff(c_22749,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_22743])).

tff(c_49709,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49703,c_22749])).

tff(c_50571,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50547,c_49709])).

tff(c_50580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_50571])).

tff(c_50582,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_22743])).

tff(c_50649,plain,(
    ! [A_4039,B_4040] : ~ r2_hidden(A_4039,k9_relat_1(k1_xboole_0,B_4040)) ),
    inference(splitRight,[status(thm)],[c_22743])).

tff(c_50726,plain,(
    ! [B_4041] : k9_relat_1(k1_xboole_0,B_4041) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_267,c_50649])).

tff(c_50792,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50726,c_28])).

tff(c_50836,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50582,c_50792])).

tff(c_116176,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116170,c_116170,c_50836])).

tff(c_116724,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116708,c_116708,c_116176])).

tff(c_116786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116731,c_116724])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:41:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.02/11.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.04/11.98  
% 21.04/11.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.04/11.99  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 21.04/11.99  
% 21.04/11.99  %Foreground sorts:
% 21.04/11.99  
% 21.04/11.99  
% 21.04/11.99  %Background operators:
% 21.04/11.99  
% 21.04/11.99  
% 21.04/11.99  %Foreground operators:
% 21.04/11.99  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 21.04/11.99  tff('#skF_7', type, '#skF_7': $i > $i).
% 21.04/11.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 21.04/11.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.04/11.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.04/11.99  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 21.04/11.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.04/11.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.04/11.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 21.04/11.99  tff('#skF_5', type, '#skF_5': $i).
% 21.04/11.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 21.04/11.99  tff('#skF_6', type, '#skF_6': $i).
% 21.04/11.99  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 21.04/11.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 21.04/11.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.04/11.99  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 21.04/11.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.04/11.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 21.04/11.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 21.04/11.99  tff('#skF_4', type, '#skF_4': $i).
% 21.04/11.99  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 21.04/11.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.04/11.99  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 21.04/11.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 21.04/11.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 21.04/11.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.04/11.99  
% 21.23/12.01  tff(f_124, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 21.23/12.01  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 21.23/12.01  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 21.23/12.01  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 21.23/12.01  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 21.23/12.01  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 21.23/12.01  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 21.23/12.01  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 21.23/12.01  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 21.23/12.01  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 21.23/12.01  tff(f_40, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 21.23/12.01  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 21.23/12.01  tff(f_75, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 21.23/12.01  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.23/12.01  tff(c_144, plain, (![A_75, B_76, C_77]: (k2_relset_1(A_75, B_76, C_77)=k2_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 21.23/12.01  tff(c_148, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_144])).
% 21.23/12.01  tff(c_52, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.23/12.01  tff(c_149, plain, (k2_relat_1('#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_52])).
% 21.23/12.01  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 21.23/12.01  tff(c_62, plain, (![D_39]: (r2_hidden('#skF_7'(D_39), '#skF_4') | ~r2_hidden(D_39, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.23/12.01  tff(c_56, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.23/12.01  tff(c_167, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 21.23/12.01  tff(c_171, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_167])).
% 21.23/12.01  tff(c_84395, plain, (![B_6026, A_6027, C_6028]: (k1_xboole_0=B_6026 | k1_relset_1(A_6027, B_6026, C_6028)=A_6027 | ~v1_funct_2(C_6028, A_6027, B_6026) | ~m1_subset_1(C_6028, k1_zfmisc_1(k2_zfmisc_1(A_6027, B_6026))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 21.23/12.01  tff(c_84398, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_84395])).
% 21.23/12.01  tff(c_84401, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_171, c_84398])).
% 21.23/12.01  tff(c_84402, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_84401])).
% 21.23/12.01  tff(c_89, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 21.23/12.01  tff(c_93, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_89])).
% 21.23/12.01  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.23/12.01  tff(c_60, plain, (![D_39]: (k1_funct_1('#skF_6', '#skF_7'(D_39))=D_39 | ~r2_hidden(D_39, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.23/12.01  tff(c_333, plain, (![B_118, A_119]: (r2_hidden(k1_funct_1(B_118, A_119), k2_relat_1(B_118)) | ~r2_hidden(A_119, k1_relat_1(B_118)) | ~v1_funct_1(B_118) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_70])).
% 21.23/12.01  tff(c_341, plain, (![D_39]: (r2_hidden(D_39, k2_relat_1('#skF_6')) | ~r2_hidden('#skF_7'(D_39), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(D_39, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_333])).
% 21.23/12.01  tff(c_345, plain, (![D_39]: (r2_hidden(D_39, k2_relat_1('#skF_6')) | ~r2_hidden('#skF_7'(D_39), k1_relat_1('#skF_6')) | ~r2_hidden(D_39, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_58, c_341])).
% 21.23/12.01  tff(c_84501, plain, (![D_6036]: (r2_hidden(D_6036, k2_relat_1('#skF_6')) | ~r2_hidden('#skF_7'(D_6036), '#skF_4') | ~r2_hidden(D_6036, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_84402, c_345])).
% 21.23/12.01  tff(c_84510, plain, (![D_39]: (r2_hidden(D_39, k2_relat_1('#skF_6')) | ~r2_hidden(D_39, '#skF_5'))), inference(resolution, [status(thm)], [c_62, c_84501])).
% 21.23/12.01  tff(c_127, plain, (![A_71, B_72]: (r2_hidden('#skF_1'(A_71, B_72), B_72) | r2_hidden('#skF_2'(A_71, B_72), A_71) | B_72=A_71)), inference(cnfTransformation, [status(thm)], [f_32])).
% 21.23/12.01  tff(c_18, plain, (![C_12, A_9, B_10]: (r2_hidden(C_12, A_9) | ~r2_hidden(C_12, B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 21.23/12.01  tff(c_84931, plain, (![A_6062, B_6063, A_6064]: (r2_hidden('#skF_2'(A_6062, B_6063), A_6064) | ~m1_subset_1(A_6062, k1_zfmisc_1(A_6064)) | r2_hidden('#skF_1'(A_6062, B_6063), B_6063) | B_6063=A_6062)), inference(resolution, [status(thm)], [c_127, c_18])).
% 21.23/12.01  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 21.23/12.01  tff(c_85039, plain, (![A_6065, A_6066]: (~m1_subset_1(A_6065, k1_zfmisc_1(A_6066)) | r2_hidden('#skF_1'(A_6065, A_6066), A_6066) | A_6066=A_6065)), inference(resolution, [status(thm)], [c_84931, c_4])).
% 21.23/12.01  tff(c_85345, plain, (![A_6090, A_6091, A_6092]: (r2_hidden('#skF_1'(A_6090, A_6091), A_6092) | ~m1_subset_1(A_6091, k1_zfmisc_1(A_6092)) | ~m1_subset_1(A_6090, k1_zfmisc_1(A_6091)) | A_6091=A_6090)), inference(resolution, [status(thm)], [c_85039, c_18])).
% 21.23/12.01  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 21.23/12.01  tff(c_85600, plain, (![A_6120, A_6121]: (~r2_hidden('#skF_2'(A_6120, A_6121), A_6121) | ~m1_subset_1(A_6121, k1_zfmisc_1(A_6120)) | ~m1_subset_1(A_6120, k1_zfmisc_1(A_6121)) | A_6121=A_6120)), inference(resolution, [status(thm)], [c_85345, c_2])).
% 21.23/12.01  tff(c_104148, plain, (![A_7374]: (~m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1(A_7374)) | ~m1_subset_1(A_7374, k1_zfmisc_1(k2_relat_1('#skF_6'))) | k2_relat_1('#skF_6')=A_7374 | ~r2_hidden('#skF_2'(A_7374, k2_relat_1('#skF_6')), '#skF_5'))), inference(resolution, [status(thm)], [c_84510, c_85600])).
% 21.23/12.01  tff(c_104168, plain, (~m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_relat_1('#skF_6'))) | ~r2_hidden('#skF_1'('#skF_5', k2_relat_1('#skF_6')), '#skF_5') | k2_relat_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_6, c_104148])).
% 21.23/12.01  tff(c_104178, plain, (~m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_relat_1('#skF_6'))) | ~r2_hidden('#skF_1'('#skF_5', k2_relat_1('#skF_6')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_149, c_149, c_104168])).
% 21.23/12.01  tff(c_104233, plain, (~r2_hidden('#skF_1'('#skF_5', k2_relat_1('#skF_6')), '#skF_5')), inference(splitLeft, [status(thm)], [c_104178])).
% 21.23/12.01  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 21.23/12.01  tff(c_28, plain, (![A_19]: (k9_relat_1(A_19, k1_relat_1(A_19))=k2_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 21.23/12.01  tff(c_22716, plain, (![A_2136, B_2137, C_2138]: (r2_hidden(k4_tarski('#skF_3'(A_2136, B_2137, C_2138), A_2136), C_2138) | ~r2_hidden(A_2136, k9_relat_1(C_2138, B_2137)) | ~v1_relat_1(C_2138))), inference(cnfTransformation, [status(thm)], [f_58])).
% 21.23/12.01  tff(c_94516, plain, (![A_6727, B_6728, C_6729, A_6730]: (r2_hidden(k4_tarski('#skF_3'(A_6727, B_6728, C_6729), A_6727), A_6730) | ~m1_subset_1(C_6729, k1_zfmisc_1(A_6730)) | ~r2_hidden(A_6727, k9_relat_1(C_6729, B_6728)) | ~v1_relat_1(C_6729))), inference(resolution, [status(thm)], [c_22716, c_18])).
% 21.23/12.01  tff(c_14, plain, (![B_6, D_8, A_5, C_7]: (r2_hidden(B_6, D_8) | ~r2_hidden(k4_tarski(A_5, B_6), k2_zfmisc_1(C_7, D_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 21.23/12.01  tff(c_112705, plain, (![B_7818, C_7816, A_7817, C_7819, D_7815]: (r2_hidden(A_7817, D_7815) | ~m1_subset_1(C_7816, k1_zfmisc_1(k2_zfmisc_1(C_7819, D_7815))) | ~r2_hidden(A_7817, k9_relat_1(C_7816, B_7818)) | ~v1_relat_1(C_7816))), inference(resolution, [status(thm)], [c_94516, c_14])).
% 21.23/12.01  tff(c_112707, plain, (![A_7817, B_7818]: (r2_hidden(A_7817, '#skF_5') | ~r2_hidden(A_7817, k9_relat_1('#skF_6', B_7818)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_112705])).
% 21.23/12.01  tff(c_112711, plain, (![A_7820, B_7821]: (r2_hidden(A_7820, '#skF_5') | ~r2_hidden(A_7820, k9_relat_1('#skF_6', B_7821)))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_112707])).
% 21.23/12.01  tff(c_112851, plain, (![A_7820]: (r2_hidden(A_7820, '#skF_5') | ~r2_hidden(A_7820, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_112711])).
% 21.23/12.01  tff(c_112891, plain, (![A_7822]: (r2_hidden(A_7822, '#skF_5') | ~r2_hidden(A_7822, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_112851])).
% 21.23/12.01  tff(c_113048, plain, (![A_1]: (r2_hidden('#skF_1'(A_1, k2_relat_1('#skF_6')), '#skF_5') | r2_hidden('#skF_2'(A_1, k2_relat_1('#skF_6')), A_1) | k2_relat_1('#skF_6')=A_1)), inference(resolution, [status(thm)], [c_8, c_112891])).
% 21.23/12.01  tff(c_84511, plain, (![D_6037]: (r2_hidden(D_6037, k2_relat_1('#skF_6')) | ~r2_hidden(D_6037, '#skF_5'))), inference(resolution, [status(thm)], [c_62, c_84501])).
% 21.23/12.01  tff(c_84537, plain, (![A_1]: (r2_hidden('#skF_1'(A_1, k2_relat_1('#skF_6')), k2_relat_1('#skF_6')) | k2_relat_1('#skF_6')=A_1 | ~r2_hidden('#skF_2'(A_1, k2_relat_1('#skF_6')), '#skF_5'))), inference(resolution, [status(thm)], [c_84511, c_4])).
% 21.23/12.01  tff(c_116047, plain, (![A_7957]: (r2_hidden('#skF_1'(A_7957, k2_relat_1('#skF_6')), '#skF_5') | k2_relat_1('#skF_6')=A_7957 | ~r2_hidden('#skF_2'(A_7957, k2_relat_1('#skF_6')), '#skF_5'))), inference(resolution, [status(thm)], [c_84537, c_112891])).
% 21.23/12.01  tff(c_116055, plain, (r2_hidden('#skF_1'('#skF_5', k2_relat_1('#skF_6')), '#skF_5') | k2_relat_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_113048, c_116047])).
% 21.23/12.01  tff(c_116091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_104233, c_149, c_104233, c_116055])).
% 21.23/12.01  tff(c_116093, plain, (r2_hidden('#skF_1'('#skF_5', k2_relat_1('#skF_6')), '#skF_5')), inference(splitRight, [status(thm)], [c_104178])).
% 21.23/12.01  tff(c_116102, plain, (~r2_hidden('#skF_2'('#skF_5', k2_relat_1('#skF_6')), k2_relat_1('#skF_6')) | k2_relat_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_116093, c_2])).
% 21.23/12.01  tff(c_116117, plain, (~r2_hidden('#skF_2'('#skF_5', k2_relat_1('#skF_6')), k2_relat_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_149, c_116102])).
% 21.23/12.01  tff(c_116134, plain, (~r2_hidden('#skF_2'('#skF_5', k2_relat_1('#skF_6')), '#skF_5')), inference(resolution, [status(thm)], [c_84510, c_116117])).
% 21.23/12.01  tff(c_116157, plain, (~r2_hidden('#skF_1'('#skF_5', k2_relat_1('#skF_6')), '#skF_5') | k2_relat_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_6, c_116134])).
% 21.23/12.01  tff(c_116167, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_116093, c_116157])).
% 21.23/12.01  tff(c_116169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_116167])).
% 21.23/12.01  tff(c_116171, plain, (k1_relat_1('#skF_6')!='#skF_4'), inference(splitRight, [status(thm)], [c_84401])).
% 21.23/12.01  tff(c_116170, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_84401])).
% 21.23/12.01  tff(c_42, plain, (![C_35, A_33]: (k1_xboole_0=C_35 | ~v1_funct_2(C_35, A_33, k1_xboole_0) | k1_xboole_0=A_33 | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 21.23/12.01  tff(c_116527, plain, (![C_7985, A_7986]: (C_7985='#skF_5' | ~v1_funct_2(C_7985, A_7986, '#skF_5') | A_7986='#skF_5' | ~m1_subset_1(C_7985, k1_zfmisc_1(k2_zfmisc_1(A_7986, '#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_116170, c_116170, c_116170, c_116170, c_42])).
% 21.23/12.01  tff(c_116530, plain, ('#skF_5'='#skF_6' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_54, c_116527])).
% 21.23/12.01  tff(c_116533, plain, ('#skF_5'='#skF_6' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_116530])).
% 21.23/12.01  tff(c_116534, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_116533])).
% 21.23/12.01  tff(c_116559, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_116534, c_56])).
% 21.23/12.01  tff(c_116558, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_116534, c_54])).
% 21.23/12.01  tff(c_48, plain, (![B_34, C_35]: (k1_relset_1(k1_xboole_0, B_34, C_35)=k1_xboole_0 | ~v1_funct_2(C_35, k1_xboole_0, B_34) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_34))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 21.23/12.01  tff(c_116187, plain, (![B_34, C_35]: (k1_relset_1('#skF_5', B_34, C_35)='#skF_5' | ~v1_funct_2(C_35, '#skF_5', B_34) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_34))))), inference(demodulation, [status(thm), theory('equality')], [c_116170, c_116170, c_116170, c_116170, c_48])).
% 21.23/12.01  tff(c_116606, plain, (![B_34, C_35]: (k1_relset_1('#skF_4', B_34, C_35)='#skF_4' | ~v1_funct_2(C_35, '#skF_4', B_34) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_34))))), inference(demodulation, [status(thm), theory('equality')], [c_116534, c_116534, c_116534, c_116534, c_116187])).
% 21.23/12.01  tff(c_116645, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_116558, c_116606])).
% 21.23/12.01  tff(c_116657, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_116559, c_116645])).
% 21.23/12.01  tff(c_116555, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_116534, c_171])).
% 21.23/12.01  tff(c_116706, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_116657, c_116555])).
% 21.23/12.01  tff(c_116707, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116171, c_116706])).
% 21.23/12.01  tff(c_116708, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_116533])).
% 21.23/12.01  tff(c_116731, plain, (k2_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_116708, c_149])).
% 21.23/12.01  tff(c_22829, plain, (![B_2144, A_2145, C_2146]: (k1_xboole_0=B_2144 | k1_relset_1(A_2145, B_2144, C_2146)=A_2145 | ~v1_funct_2(C_2146, A_2145, B_2144) | ~m1_subset_1(C_2146, k1_zfmisc_1(k2_zfmisc_1(A_2145, B_2144))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 21.23/12.01  tff(c_22832, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_22829])).
% 21.23/12.01  tff(c_22835, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_171, c_22832])).
% 21.23/12.01  tff(c_22836, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_22835])).
% 21.23/12.01  tff(c_22868, plain, (![D_2147]: (r2_hidden(D_2147, k2_relat_1('#skF_6')) | ~r2_hidden('#skF_7'(D_2147), '#skF_4') | ~r2_hidden(D_2147, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_22836, c_345])).
% 21.23/12.01  tff(c_22877, plain, (![D_39]: (r2_hidden(D_39, k2_relat_1('#skF_6')) | ~r2_hidden(D_39, '#skF_5'))), inference(resolution, [status(thm)], [c_62, c_22868])).
% 21.23/12.01  tff(c_23624, plain, (![A_2213, B_2214, A_2215]: (r2_hidden('#skF_2'(A_2213, B_2214), A_2215) | ~m1_subset_1(A_2213, k1_zfmisc_1(A_2215)) | r2_hidden('#skF_1'(A_2213, B_2214), B_2214) | B_2214=A_2213)), inference(resolution, [status(thm)], [c_127, c_18])).
% 21.23/12.01  tff(c_23747, plain, (![A_2216, A_2217]: (~m1_subset_1(A_2216, k1_zfmisc_1(A_2217)) | r2_hidden('#skF_1'(A_2216, A_2217), A_2217) | A_2217=A_2216)), inference(resolution, [status(thm)], [c_23624, c_4])).
% 21.23/12.01  tff(c_26357, plain, (![A_2452, A_2453, A_2454]: (r2_hidden('#skF_1'(A_2452, A_2453), A_2454) | ~m1_subset_1(A_2453, k1_zfmisc_1(A_2454)) | ~m1_subset_1(A_2452, k1_zfmisc_1(A_2453)) | A_2453=A_2452)), inference(resolution, [status(thm)], [c_23747, c_18])).
% 21.23/12.01  tff(c_26433, plain, (![A_2462, A_2463]: (~r2_hidden('#skF_2'(A_2462, A_2463), A_2463) | ~m1_subset_1(A_2463, k1_zfmisc_1(A_2462)) | ~m1_subset_1(A_2462, k1_zfmisc_1(A_2463)) | A_2463=A_2462)), inference(resolution, [status(thm)], [c_26357, c_2])).
% 21.23/12.01  tff(c_39073, plain, (![A_3406]: (~m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1(A_3406)) | ~m1_subset_1(A_3406, k1_zfmisc_1(k2_relat_1('#skF_6'))) | k2_relat_1('#skF_6')=A_3406 | ~r2_hidden('#skF_2'(A_3406, k2_relat_1('#skF_6')), '#skF_5'))), inference(resolution, [status(thm)], [c_22877, c_26433])).
% 21.23/12.01  tff(c_39093, plain, (~m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_relat_1('#skF_6'))) | ~r2_hidden('#skF_1'('#skF_5', k2_relat_1('#skF_6')), '#skF_5') | k2_relat_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_6, c_39073])).
% 21.23/12.01  tff(c_39103, plain, (~m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_relat_1('#skF_6'))) | ~r2_hidden('#skF_1'('#skF_5', k2_relat_1('#skF_6')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_149, c_149, c_39093])).
% 21.23/12.01  tff(c_39285, plain, (~r2_hidden('#skF_1'('#skF_5', k2_relat_1('#skF_6')), '#skF_5')), inference(splitLeft, [status(thm)], [c_39103])).
% 21.23/12.01  tff(c_28840, plain, (![A_2646, B_2647, C_2648, A_2649]: (r2_hidden(k4_tarski('#skF_3'(A_2646, B_2647, C_2648), A_2646), A_2649) | ~m1_subset_1(C_2648, k1_zfmisc_1(A_2649)) | ~r2_hidden(A_2646, k9_relat_1(C_2648, B_2647)) | ~v1_relat_1(C_2648))), inference(resolution, [status(thm)], [c_22716, c_18])).
% 21.23/12.01  tff(c_46255, plain, (![C_3823, A_3821, C_3820, D_3819, B_3822]: (r2_hidden(A_3821, D_3819) | ~m1_subset_1(C_3823, k1_zfmisc_1(k2_zfmisc_1(C_3820, D_3819))) | ~r2_hidden(A_3821, k9_relat_1(C_3823, B_3822)) | ~v1_relat_1(C_3823))), inference(resolution, [status(thm)], [c_28840, c_14])).
% 21.23/12.01  tff(c_46257, plain, (![A_3821, B_3822]: (r2_hidden(A_3821, '#skF_5') | ~r2_hidden(A_3821, k9_relat_1('#skF_6', B_3822)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_46255])).
% 21.23/12.01  tff(c_46261, plain, (![A_3824, B_3825]: (r2_hidden(A_3824, '#skF_5') | ~r2_hidden(A_3824, k9_relat_1('#skF_6', B_3825)))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_46257])).
% 21.23/12.01  tff(c_46401, plain, (![A_3824]: (r2_hidden(A_3824, '#skF_5') | ~r2_hidden(A_3824, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_46261])).
% 21.23/12.01  tff(c_46441, plain, (![A_3826]: (r2_hidden(A_3826, '#skF_5') | ~r2_hidden(A_3826, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_46401])).
% 21.23/12.01  tff(c_46598, plain, (![A_1]: (r2_hidden('#skF_1'(A_1, k2_relat_1('#skF_6')), '#skF_5') | r2_hidden('#skF_2'(A_1, k2_relat_1('#skF_6')), A_1) | k2_relat_1('#skF_6')=A_1)), inference(resolution, [status(thm)], [c_8, c_46441])).
% 21.23/12.01  tff(c_22878, plain, (![D_2148]: (r2_hidden(D_2148, k2_relat_1('#skF_6')) | ~r2_hidden(D_2148, '#skF_5'))), inference(resolution, [status(thm)], [c_62, c_22868])).
% 21.23/12.01  tff(c_22896, plain, (![A_1]: (r2_hidden('#skF_1'(A_1, k2_relat_1('#skF_6')), k2_relat_1('#skF_6')) | k2_relat_1('#skF_6')=A_1 | ~r2_hidden('#skF_2'(A_1, k2_relat_1('#skF_6')), '#skF_5'))), inference(resolution, [status(thm)], [c_22878, c_4])).
% 21.23/12.01  tff(c_49573, plain, (![A_3961]: (r2_hidden('#skF_1'(A_3961, k2_relat_1('#skF_6')), '#skF_5') | k2_relat_1('#skF_6')=A_3961 | ~r2_hidden('#skF_2'(A_3961, k2_relat_1('#skF_6')), '#skF_5'))), inference(resolution, [status(thm)], [c_22896, c_46441])).
% 21.23/12.01  tff(c_49577, plain, (r2_hidden('#skF_1'('#skF_5', k2_relat_1('#skF_6')), '#skF_5') | k2_relat_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_46598, c_49573])).
% 21.23/12.01  tff(c_49617, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_39285, c_149, c_39285, c_49577])).
% 21.23/12.01  tff(c_49619, plain, (r2_hidden('#skF_1'('#skF_5', k2_relat_1('#skF_6')), '#skF_5')), inference(splitRight, [status(thm)], [c_39103])).
% 21.23/12.01  tff(c_49628, plain, (~r2_hidden('#skF_2'('#skF_5', k2_relat_1('#skF_6')), k2_relat_1('#skF_6')) | k2_relat_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_49619, c_2])).
% 21.23/12.01  tff(c_49643, plain, (~r2_hidden('#skF_2'('#skF_5', k2_relat_1('#skF_6')), k2_relat_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_149, c_49628])).
% 21.23/12.01  tff(c_49676, plain, (~r2_hidden('#skF_2'('#skF_5', k2_relat_1('#skF_6')), '#skF_5')), inference(resolution, [status(thm)], [c_22877, c_49643])).
% 21.23/12.01  tff(c_49690, plain, (~r2_hidden('#skF_1'('#skF_5', k2_relat_1('#skF_6')), '#skF_5') | k2_relat_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_6, c_49676])).
% 21.23/12.01  tff(c_49700, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_49619, c_49690])).
% 21.23/12.01  tff(c_49702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_49700])).
% 21.23/12.01  tff(c_49704, plain, (k1_relat_1('#skF_6')!='#skF_4'), inference(splitRight, [status(thm)], [c_22835])).
% 21.23/12.01  tff(c_49703, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_22835])).
% 21.23/12.01  tff(c_50091, plain, (![C_4000, A_4001]: (C_4000='#skF_5' | ~v1_funct_2(C_4000, A_4001, '#skF_5') | A_4001='#skF_5' | ~m1_subset_1(C_4000, k1_zfmisc_1(k2_zfmisc_1(A_4001, '#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_49703, c_49703, c_49703, c_49703, c_42])).
% 21.23/12.01  tff(c_50094, plain, ('#skF_5'='#skF_6' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_54, c_50091])).
% 21.23/12.01  tff(c_50097, plain, ('#skF_5'='#skF_6' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50094])).
% 21.23/12.01  tff(c_50098, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_50097])).
% 21.23/12.01  tff(c_50127, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50098, c_56])).
% 21.23/12.01  tff(c_50123, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50098, c_171])).
% 21.23/12.01  tff(c_50126, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_50098, c_54])).
% 21.23/12.01  tff(c_49718, plain, (![B_34, C_35]: (k1_relset_1('#skF_5', B_34, C_35)='#skF_5' | ~v1_funct_2(C_35, '#skF_5', B_34) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_34))))), inference(demodulation, [status(thm), theory('equality')], [c_49703, c_49703, c_49703, c_49703, c_48])).
% 21.23/12.01  tff(c_50538, plain, (![B_4037, C_4038]: (k1_relset_1('#skF_4', B_4037, C_4038)='#skF_4' | ~v1_funct_2(C_4038, '#skF_4', B_4037) | ~m1_subset_1(C_4038, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_4037))))), inference(demodulation, [status(thm), theory('equality')], [c_50098, c_50098, c_50098, c_50098, c_49718])).
% 21.23/12.01  tff(c_50541, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_50126, c_50538])).
% 21.23/12.01  tff(c_50544, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50127, c_50123, c_50541])).
% 21.23/12.01  tff(c_50546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49704, c_50544])).
% 21.23/12.01  tff(c_50547, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_50097])).
% 21.23/12.01  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 21.23/12.01  tff(c_32, plain, (![B_23, A_22]: (~r1_tarski(B_23, A_22) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 21.23/12.01  tff(c_263, plain, (![A_101, B_102]: (~r1_tarski(A_101, '#skF_2'(A_101, B_102)) | r2_hidden('#skF_1'(A_101, B_102), B_102) | B_102=A_101)), inference(resolution, [status(thm)], [c_127, c_32])).
% 21.23/12.01  tff(c_267, plain, (![B_102]: (r2_hidden('#skF_1'(k1_xboole_0, B_102), B_102) | k1_xboole_0=B_102)), inference(resolution, [status(thm)], [c_10, c_263])).
% 21.23/12.01  tff(c_204, plain, (![A_88, B_89, C_90]: (r2_hidden('#skF_3'(A_88, B_89, C_90), B_89) | ~r2_hidden(A_88, k9_relat_1(C_90, B_89)) | ~v1_relat_1(C_90))), inference(cnfTransformation, [status(thm)], [f_58])).
% 21.23/12.01  tff(c_353, plain, (![B_121, A_122, C_123]: (~r1_tarski(B_121, '#skF_3'(A_122, B_121, C_123)) | ~r2_hidden(A_122, k9_relat_1(C_123, B_121)) | ~v1_relat_1(C_123))), inference(resolution, [status(thm)], [c_204, c_32])).
% 21.23/12.01  tff(c_358, plain, (![A_124, C_125]: (~r2_hidden(A_124, k9_relat_1(C_125, k1_xboole_0)) | ~v1_relat_1(C_125))), inference(resolution, [status(thm)], [c_10, c_353])).
% 21.23/12.01  tff(c_405, plain, (![C_128]: (~v1_relat_1(C_128) | k9_relat_1(C_128, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_267, c_358])).
% 21.23/12.01  tff(c_409, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_93, c_405])).
% 21.23/12.01  tff(c_357, plain, (![A_122, C_123]: (~r2_hidden(A_122, k9_relat_1(C_123, k1_xboole_0)) | ~v1_relat_1(C_123))), inference(resolution, [status(thm)], [c_10, c_353])).
% 21.23/12.01  tff(c_413, plain, (![A_122]: (~r2_hidden(A_122, k1_xboole_0) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_409, c_357])).
% 21.23/12.01  tff(c_417, plain, (![A_122]: (~r2_hidden(A_122, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_413])).
% 21.23/12.01  tff(c_22743, plain, (![A_2136, B_2137]: (~r2_hidden(A_2136, k9_relat_1(k1_xboole_0, B_2137)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_22716, c_417])).
% 21.23/12.01  tff(c_22749, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_22743])).
% 21.23/12.01  tff(c_49709, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_49703, c_22749])).
% 21.23/12.01  tff(c_50571, plain, (~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50547, c_49709])).
% 21.23/12.01  tff(c_50580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_50571])).
% 21.23/12.01  tff(c_50582, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_22743])).
% 21.23/12.01  tff(c_50649, plain, (![A_4039, B_4040]: (~r2_hidden(A_4039, k9_relat_1(k1_xboole_0, B_4040)))), inference(splitRight, [status(thm)], [c_22743])).
% 21.23/12.01  tff(c_50726, plain, (![B_4041]: (k9_relat_1(k1_xboole_0, B_4041)=k1_xboole_0)), inference(resolution, [status(thm)], [c_267, c_50649])).
% 21.23/12.01  tff(c_50792, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50726, c_28])).
% 21.23/12.01  tff(c_50836, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50582, c_50792])).
% 21.23/12.01  tff(c_116176, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_116170, c_116170, c_50836])).
% 21.23/12.01  tff(c_116724, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_116708, c_116708, c_116176])).
% 21.23/12.01  tff(c_116786, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116731, c_116724])).
% 21.23/12.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.23/12.01  
% 21.23/12.01  Inference rules
% 21.23/12.01  ----------------------
% 21.23/12.01  #Ref     : 0
% 21.23/12.01  #Sup     : 22368
% 21.23/12.01  #Fact    : 0
% 21.23/12.01  #Define  : 0
% 21.23/12.01  #Split   : 134
% 21.23/12.01  #Chain   : 0
% 21.23/12.01  #Close   : 0
% 21.23/12.01  
% 21.23/12.01  Ordering : KBO
% 21.23/12.01  
% 21.23/12.01  Simplification rules
% 21.23/12.01  ----------------------
% 21.23/12.01  #Subsume      : 8729
% 21.23/12.01  #Demod        : 16778
% 21.23/12.01  #Tautology    : 2049
% 21.23/12.01  #SimpNegUnit  : 620
% 21.23/12.01  #BackRed      : 6517
% 21.23/12.01  
% 21.23/12.01  #Partial instantiations: 0
% 21.23/12.01  #Strategies tried      : 1
% 21.23/12.01  
% 21.23/12.01  Timing (in seconds)
% 21.23/12.01  ----------------------
% 21.23/12.02  Preprocessing        : 0.33
% 21.23/12.02  Parsing              : 0.17
% 21.23/12.02  CNF conversion       : 0.02
% 21.23/12.02  Main loop            : 10.87
% 21.23/12.02  Inferencing          : 2.73
% 21.23/12.02  Reduction            : 3.01
% 21.23/12.02  Demodulation         : 1.91
% 21.23/12.02  BG Simplification    : 0.31
% 21.23/12.02  Subsumption          : 3.79
% 21.23/12.02  Abstraction          : 0.39
% 21.23/12.02  MUC search           : 0.00
% 21.23/12.02  Cooper               : 0.00
% 21.23/12.02  Total                : 11.26
% 21.23/12.02  Index Insertion      : 0.00
% 21.23/12.02  Index Deletion       : 0.00
% 21.23/12.02  Index Matching       : 0.00
% 21.23/12.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
