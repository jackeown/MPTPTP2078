%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:23 EST 2020

% Result     : Theorem 24.35s
% Output     : CNFRefutation 24.57s
% Verified   : 
% Statistics : Number of formulae       :  192 (2331 expanded)
%              Number of leaves         :   43 ( 820 expanded)
%              Depth                    :   16
%              Number of atoms          :  367 (7529 expanded)
%              Number of equality atoms :  110 (2879 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_10 > #skF_9 > #skF_7 > #skF_8 > #skF_11 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
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

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_70,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_116,plain,(
    ! [A_100,B_101,C_102] :
      ( k2_relset_1(A_100,B_101,C_102) = k2_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_120,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_70,c_116])).

tff(c_68,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_121,plain,(
    k2_relat_1('#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_68])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    ! [D_77] :
      ( r2_hidden('#skF_11'(D_77),'#skF_8')
      | ~ r2_hidden(D_77,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_72,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_157,plain,(
    ! [A_112,B_113,C_114] :
      ( k1_relset_1(A_112,B_113,C_114) = k1_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_161,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_70,c_157])).

tff(c_75609,plain,(
    ! [B_5443,A_5444,C_5445] :
      ( k1_xboole_0 = B_5443
      | k1_relset_1(A_5444,B_5443,C_5445) = A_5444
      | ~ v1_funct_2(C_5445,A_5444,B_5443)
      | ~ m1_subset_1(C_5445,k1_zfmisc_1(k2_zfmisc_1(A_5444,B_5443))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_75612,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_75609])).

tff(c_75615,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_161,c_75612])).

tff(c_75616,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_75615])).

tff(c_87,plain,(
    ! [C_84,A_85,B_86] :
      ( v1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_91,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_70,c_87])).

tff(c_74,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_76,plain,(
    ! [D_77] :
      ( k1_funct_1('#skF_10','#skF_11'(D_77)) = D_77
      | ~ r2_hidden(D_77,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_330,plain,(
    ! [A_155,D_156] :
      ( r2_hidden(k1_funct_1(A_155,D_156),k2_relat_1(A_155))
      | ~ r2_hidden(D_156,k1_relat_1(A_155))
      | ~ v1_funct_1(A_155)
      | ~ v1_relat_1(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_338,plain,(
    ! [D_77] :
      ( r2_hidden(D_77,k2_relat_1('#skF_10'))
      | ~ r2_hidden('#skF_11'(D_77),k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(D_77,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_330])).

tff(c_342,plain,(
    ! [D_77] :
      ( r2_hidden(D_77,k2_relat_1('#skF_10'))
      | ~ r2_hidden('#skF_11'(D_77),k1_relat_1('#skF_10'))
      | ~ r2_hidden(D_77,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_74,c_338])).

tff(c_75653,plain,(
    ! [D_5446] :
      ( r2_hidden(D_5446,k2_relat_1('#skF_10'))
      | ~ r2_hidden('#skF_11'(D_5446),'#skF_8')
      | ~ r2_hidden(D_5446,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75616,c_342])).

tff(c_75662,plain,(
    ! [D_77] :
      ( r2_hidden(D_77,k2_relat_1('#skF_10'))
      | ~ r2_hidden(D_77,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_78,c_75653])).

tff(c_167,plain,(
    ! [A_117,B_118] :
      ( r2_hidden('#skF_1'(A_117,B_118),B_118)
      | r2_hidden('#skF_2'(A_117,B_118),A_117)
      | B_118 = A_117 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [C_12,A_9,B_10] :
      ( r2_hidden(C_12,A_9)
      | ~ r2_hidden(C_12,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_77261,plain,(
    ! [A_5570,B_5571,A_5572] :
      ( r2_hidden('#skF_2'(A_5570,B_5571),A_5572)
      | ~ m1_subset_1(A_5570,k1_zfmisc_1(A_5572))
      | r2_hidden('#skF_1'(A_5570,B_5571),B_5571)
      | B_5571 = A_5570 ) ),
    inference(resolution,[status(thm)],[c_167,c_18])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77384,plain,(
    ! [A_5573,A_5574] :
      ( ~ m1_subset_1(A_5573,k1_zfmisc_1(A_5574))
      | r2_hidden('#skF_1'(A_5573,A_5574),A_5574)
      | A_5574 = A_5573 ) ),
    inference(resolution,[status(thm)],[c_77261,c_4])).

tff(c_77541,plain,(
    ! [A_5584,A_5585,A_5586] :
      ( r2_hidden('#skF_1'(A_5584,A_5585),A_5586)
      | ~ m1_subset_1(A_5585,k1_zfmisc_1(A_5586))
      | ~ m1_subset_1(A_5584,k1_zfmisc_1(A_5585))
      | A_5585 = A_5584 ) ),
    inference(resolution,[status(thm)],[c_77384,c_18])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77638,plain,(
    ! [A_5600,A_5601] :
      ( ~ r2_hidden('#skF_2'(A_5600,A_5601),A_5601)
      | ~ m1_subset_1(A_5601,k1_zfmisc_1(A_5600))
      | ~ m1_subset_1(A_5600,k1_zfmisc_1(A_5601))
      | A_5601 = A_5600 ) ),
    inference(resolution,[status(thm)],[c_77541,c_2])).

tff(c_85478,plain,(
    ! [A_6077] :
      ( ~ m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1(A_6077))
      | ~ m1_subset_1(A_6077,k1_zfmisc_1(k2_relat_1('#skF_10')))
      | k2_relat_1('#skF_10') = A_6077
      | ~ r2_hidden('#skF_2'(A_6077,k2_relat_1('#skF_10')),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_75662,c_77638])).

tff(c_85498,plain,
    ( ~ m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1('#skF_9'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_relat_1('#skF_10')))
    | ~ r2_hidden('#skF_1'('#skF_9',k2_relat_1('#skF_10')),'#skF_9')
    | k2_relat_1('#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_6,c_85478])).

tff(c_85508,plain,
    ( ~ m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1('#skF_9'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_relat_1('#skF_10')))
    | ~ r2_hidden('#skF_1'('#skF_9',k2_relat_1('#skF_10')),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_121,c_85498])).

tff(c_85782,plain,(
    ~ r2_hidden('#skF_1'('#skF_9',k2_relat_1('#skF_10')),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_85508])).

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

tff(c_9720,plain,(
    ! [A_1018,B_1019,C_1020] :
      ( r2_hidden(k4_tarski('#skF_3'(A_1018,B_1019,C_1020),A_1018),C_1020)
      | ~ r2_hidden(A_1018,k9_relat_1(C_1020,B_1019))
      | ~ v1_relat_1(C_1020) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_94133,plain,(
    ! [A_6589,B_6590,C_6591,A_6592] :
      ( r2_hidden(k4_tarski('#skF_3'(A_6589,B_6590,C_6591),A_6589),A_6592)
      | ~ m1_subset_1(C_6591,k1_zfmisc_1(A_6592))
      | ~ r2_hidden(A_6589,k9_relat_1(C_6591,B_6590))
      | ~ v1_relat_1(C_6591) ) ),
    inference(resolution,[status(thm)],[c_9720,c_18])).

tff(c_14,plain,(
    ! [B_6,D_8,A_5,C_7] :
      ( r2_hidden(B_6,D_8)
      | ~ r2_hidden(k4_tarski(A_5,B_6),k2_zfmisc_1(C_7,D_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_134430,plain,(
    ! [C_9106,D_9104,B_9108,C_9107,A_9105] :
      ( r2_hidden(A_9105,D_9104)
      | ~ m1_subset_1(C_9106,k1_zfmisc_1(k2_zfmisc_1(C_9107,D_9104)))
      | ~ r2_hidden(A_9105,k9_relat_1(C_9106,B_9108))
      | ~ v1_relat_1(C_9106) ) ),
    inference(resolution,[status(thm)],[c_94133,c_14])).

tff(c_134432,plain,(
    ! [A_9105,B_9108] :
      ( r2_hidden(A_9105,'#skF_9')
      | ~ r2_hidden(A_9105,k9_relat_1('#skF_10',B_9108))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_70,c_134430])).

tff(c_134436,plain,(
    ! [A_9109,B_9110] :
      ( r2_hidden(A_9109,'#skF_9')
      | ~ r2_hidden(A_9109,k9_relat_1('#skF_10',B_9110)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_134432])).

tff(c_134616,plain,(
    ! [A_9109] :
      ( r2_hidden(A_9109,'#skF_9')
      | ~ r2_hidden(A_9109,k2_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_134436])).

tff(c_134689,plain,(
    ! [A_9113] :
      ( r2_hidden(A_9113,'#skF_9')
      | ~ r2_hidden(A_9113,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_134616])).

tff(c_134902,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1,k2_relat_1('#skF_10')),'#skF_9')
      | r2_hidden('#skF_2'(A_1,k2_relat_1('#skF_10')),A_1)
      | k2_relat_1('#skF_10') = A_1 ) ),
    inference(resolution,[status(thm)],[c_8,c_134689])).

tff(c_75663,plain,(
    ! [D_5447] :
      ( r2_hidden(D_5447,k2_relat_1('#skF_10'))
      | ~ r2_hidden(D_5447,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_78,c_75653])).

tff(c_75682,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1,k2_relat_1('#skF_10')),k2_relat_1('#skF_10'))
      | k2_relat_1('#skF_10') = A_1
      | ~ r2_hidden('#skF_2'(A_1,k2_relat_1('#skF_10')),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_75663,c_4])).

tff(c_138370,plain,(
    ! [A_9279] :
      ( r2_hidden('#skF_1'(A_9279,k2_relat_1('#skF_10')),'#skF_9')
      | k2_relat_1('#skF_10') = A_9279
      | ~ r2_hidden('#skF_2'(A_9279,k2_relat_1('#skF_10')),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_75682,c_134689])).

tff(c_138376,plain,
    ( r2_hidden('#skF_1'('#skF_9',k2_relat_1('#skF_10')),'#skF_9')
    | k2_relat_1('#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_134902,c_138370])).

tff(c_138412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_85782,c_121,c_85782,c_138376])).

tff(c_138414,plain,(
    r2_hidden('#skF_1'('#skF_9',k2_relat_1('#skF_10')),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_85508])).

tff(c_138423,plain,
    ( ~ r2_hidden('#skF_2'('#skF_9',k2_relat_1('#skF_10')),k2_relat_1('#skF_10'))
    | k2_relat_1('#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_138414,c_2])).

tff(c_138438,plain,(
    ~ r2_hidden('#skF_2'('#skF_9',k2_relat_1('#skF_10')),k2_relat_1('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_138423])).

tff(c_138455,plain,(
    ~ r2_hidden('#skF_2'('#skF_9',k2_relat_1('#skF_10')),'#skF_9') ),
    inference(resolution,[status(thm)],[c_75662,c_138438])).

tff(c_138469,plain,
    ( ~ r2_hidden('#skF_1'('#skF_9',k2_relat_1('#skF_10')),'#skF_9')
    | k2_relat_1('#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_6,c_138455])).

tff(c_138479,plain,(
    k2_relat_1('#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138414,c_138469])).

tff(c_138481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_138479])).

tff(c_138482,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_75615])).

tff(c_12557,plain,(
    ! [B_1299,A_1300,C_1301] :
      ( k1_xboole_0 = B_1299
      | k1_relset_1(A_1300,B_1299,C_1301) = A_1300
      | ~ v1_funct_2(C_1301,A_1300,B_1299)
      | ~ m1_subset_1(C_1301,k1_zfmisc_1(k2_zfmisc_1(A_1300,B_1299))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_12560,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_12557])).

tff(c_12563,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_161,c_12560])).

tff(c_12564,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_12563])).

tff(c_12602,plain,(
    ! [D_1304] :
      ( r2_hidden(D_1304,k2_relat_1('#skF_10'))
      | ~ r2_hidden('#skF_11'(D_1304),'#skF_8')
      | ~ r2_hidden(D_1304,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12564,c_342])).

tff(c_12611,plain,(
    ! [D_77] :
      ( r2_hidden(D_77,k2_relat_1('#skF_10'))
      | ~ r2_hidden(D_77,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_78,c_12602])).

tff(c_12275,plain,(
    ! [A_1273,B_1274,A_1275] :
      ( r2_hidden('#skF_2'(A_1273,B_1274),A_1275)
      | ~ m1_subset_1(A_1273,k1_zfmisc_1(A_1275))
      | r2_hidden('#skF_1'(A_1273,B_1274),B_1274)
      | B_1274 = A_1273 ) ),
    inference(resolution,[status(thm)],[c_167,c_18])).

tff(c_12373,plain,(
    ! [A_1279,A_1280] :
      ( ~ m1_subset_1(A_1279,k1_zfmisc_1(A_1280))
      | r2_hidden('#skF_1'(A_1279,A_1280),A_1280)
      | A_1280 = A_1279 ) ),
    inference(resolution,[status(thm)],[c_12275,c_4])).

tff(c_12506,plain,(
    ! [A_1296,A_1297,A_1298] :
      ( r2_hidden('#skF_1'(A_1296,A_1297),A_1298)
      | ~ m1_subset_1(A_1297,k1_zfmisc_1(A_1298))
      | ~ m1_subset_1(A_1296,k1_zfmisc_1(A_1297))
      | A_1297 = A_1296 ) ),
    inference(resolution,[status(thm)],[c_12373,c_18])).

tff(c_13731,plain,(
    ! [A_1362,A_1363] :
      ( ~ r2_hidden('#skF_2'(A_1362,A_1363),A_1363)
      | ~ m1_subset_1(A_1363,k1_zfmisc_1(A_1362))
      | ~ m1_subset_1(A_1362,k1_zfmisc_1(A_1363))
      | A_1363 = A_1362 ) ),
    inference(resolution,[status(thm)],[c_12506,c_2])).

tff(c_21917,plain,(
    ! [A_1934] :
      ( ~ m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1(A_1934))
      | ~ m1_subset_1(A_1934,k1_zfmisc_1(k2_relat_1('#skF_10')))
      | k2_relat_1('#skF_10') = A_1934
      | ~ r2_hidden('#skF_2'(A_1934,k2_relat_1('#skF_10')),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_12611,c_13731])).

tff(c_21937,plain,
    ( ~ m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1('#skF_9'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_relat_1('#skF_10')))
    | ~ r2_hidden('#skF_1'('#skF_9',k2_relat_1('#skF_10')),'#skF_9')
    | k2_relat_1('#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_6,c_21917])).

tff(c_21947,plain,
    ( ~ m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1('#skF_9'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_relat_1('#skF_10')))
    | ~ r2_hidden('#skF_1'('#skF_9',k2_relat_1('#skF_10')),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_121,c_21937])).

tff(c_22158,plain,(
    ~ r2_hidden('#skF_1'('#skF_9',k2_relat_1('#skF_10')),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_21947])).

tff(c_26060,plain,(
    ! [A_2222,B_2223,C_2224,A_2225] :
      ( r2_hidden(k4_tarski('#skF_3'(A_2222,B_2223,C_2224),A_2222),A_2225)
      | ~ m1_subset_1(C_2224,k1_zfmisc_1(A_2225))
      | ~ r2_hidden(A_2222,k9_relat_1(C_2224,B_2223))
      | ~ v1_relat_1(C_2224) ) ),
    inference(resolution,[status(thm)],[c_9720,c_18])).

tff(c_66144,plain,(
    ! [B_4890,A_4891,D_4888,C_4887,C_4889] :
      ( r2_hidden(A_4891,D_4888)
      | ~ m1_subset_1(C_4887,k1_zfmisc_1(k2_zfmisc_1(C_4889,D_4888)))
      | ~ r2_hidden(A_4891,k9_relat_1(C_4887,B_4890))
      | ~ v1_relat_1(C_4887) ) ),
    inference(resolution,[status(thm)],[c_26060,c_14])).

tff(c_66146,plain,(
    ! [A_4891,B_4890] :
      ( r2_hidden(A_4891,'#skF_9')
      | ~ r2_hidden(A_4891,k9_relat_1('#skF_10',B_4890))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_70,c_66144])).

tff(c_66150,plain,(
    ! [A_4892,B_4893] :
      ( r2_hidden(A_4892,'#skF_9')
      | ~ r2_hidden(A_4892,k9_relat_1('#skF_10',B_4893)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_66146])).

tff(c_66334,plain,(
    ! [A_4892] :
      ( r2_hidden(A_4892,'#skF_9')
      | ~ r2_hidden(A_4892,k2_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_66150])).

tff(c_66386,plain,(
    ! [A_4894] :
      ( r2_hidden(A_4894,'#skF_9')
      | ~ r2_hidden(A_4894,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_66334])).

tff(c_66599,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1,k2_relat_1('#skF_10')),'#skF_9')
      | r2_hidden('#skF_2'(A_1,k2_relat_1('#skF_10')),A_1)
      | k2_relat_1('#skF_10') = A_1 ) ),
    inference(resolution,[status(thm)],[c_8,c_66386])).

tff(c_12612,plain,(
    ! [D_1305] :
      ( r2_hidden(D_1305,k2_relat_1('#skF_10'))
      | ~ r2_hidden(D_1305,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_78,c_12602])).

tff(c_12635,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1,k2_relat_1('#skF_10')),k2_relat_1('#skF_10'))
      | k2_relat_1('#skF_10') = A_1
      | ~ r2_hidden('#skF_2'(A_1,k2_relat_1('#skF_10')),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_12612,c_4])).

tff(c_70319,plain,(
    ! [A_5062] :
      ( r2_hidden('#skF_1'(A_5062,k2_relat_1('#skF_10')),'#skF_9')
      | k2_relat_1('#skF_10') = A_5062
      | ~ r2_hidden('#skF_2'(A_5062,k2_relat_1('#skF_10')),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_12635,c_66386])).

tff(c_70325,plain,
    ( r2_hidden('#skF_1'('#skF_9',k2_relat_1('#skF_10')),'#skF_9')
    | k2_relat_1('#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_66599,c_70319])).

tff(c_70361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_22158,c_121,c_22158,c_70325])).

tff(c_70363,plain,(
    r2_hidden('#skF_1'('#skF_9',k2_relat_1('#skF_10')),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_21947])).

tff(c_70896,plain,
    ( ~ r2_hidden('#skF_2'('#skF_9',k2_relat_1('#skF_10')),k2_relat_1('#skF_10'))
    | k2_relat_1('#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_70363,c_2])).

tff(c_70911,plain,(
    ~ r2_hidden('#skF_2'('#skF_9',k2_relat_1('#skF_10')),k2_relat_1('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_70896])).

tff(c_70925,plain,(
    ~ r2_hidden('#skF_2'('#skF_9',k2_relat_1('#skF_10')),'#skF_9') ),
    inference(resolution,[status(thm)],[c_12611,c_70911])).

tff(c_70942,plain,
    ( ~ r2_hidden('#skF_1'('#skF_9',k2_relat_1('#skF_10')),'#skF_9')
    | k2_relat_1('#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_6,c_70925])).

tff(c_70952,plain,(
    k2_relat_1('#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70363,c_70942])).

tff(c_70954,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_70952])).

tff(c_70955,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_12563])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_48,plain,(
    ! [B_61,A_60] :
      ( ~ r1_tarski(B_61,A_60)
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_272,plain,(
    ! [B_137,A_138] :
      ( ~ r1_tarski(B_137,'#skF_1'(A_138,B_137))
      | r2_hidden('#skF_2'(A_138,B_137),A_138)
      | B_137 = A_138 ) ),
    inference(resolution,[status(thm)],[c_167,c_48])).

tff(c_276,plain,(
    ! [A_138] :
      ( r2_hidden('#skF_2'(A_138,k1_xboole_0),A_138)
      | k1_xboole_0 = A_138 ) ),
    inference(resolution,[status(thm)],[c_10,c_272])).

tff(c_310,plain,(
    ! [A_143,B_144,C_145] :
      ( r2_hidden('#skF_3'(A_143,B_144,C_145),B_144)
      | ~ r2_hidden(A_143,k9_relat_1(C_145,B_144))
      | ~ v1_relat_1(C_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_325,plain,(
    ! [B_152,A_153,C_154] :
      ( ~ r1_tarski(B_152,'#skF_3'(A_153,B_152,C_154))
      | ~ r2_hidden(A_153,k9_relat_1(C_154,B_152))
      | ~ v1_relat_1(C_154) ) ),
    inference(resolution,[status(thm)],[c_310,c_48])).

tff(c_343,plain,(
    ! [A_157,C_158] :
      ( ~ r2_hidden(A_157,k9_relat_1(C_158,k1_xboole_0))
      | ~ v1_relat_1(C_158) ) ),
    inference(resolution,[status(thm)],[c_10,c_325])).

tff(c_389,plain,(
    ! [C_159] :
      ( ~ v1_relat_1(C_159)
      | k9_relat_1(C_159,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_276,c_343])).

tff(c_393,plain,(
    k9_relat_1('#skF_10',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_389])).

tff(c_329,plain,(
    ! [A_153,C_154] :
      ( ~ r2_hidden(A_153,k9_relat_1(C_154,k1_xboole_0))
      | ~ v1_relat_1(C_154) ) ),
    inference(resolution,[status(thm)],[c_10,c_325])).

tff(c_397,plain,(
    ! [A_153] :
      ( ~ r2_hidden(A_153,k1_xboole_0)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_329])).

tff(c_401,plain,(
    ! [A_153] : ~ r2_hidden(A_153,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_397])).

tff(c_9747,plain,(
    ! [A_1018,B_1019] :
      ( ~ r2_hidden(A_1018,k9_relat_1(k1_xboole_0,B_1019))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_9720,c_401])).

tff(c_9753,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_9747])).

tff(c_71017,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70955,c_9753])).

tff(c_70956,plain,(
    k1_relat_1('#skF_10') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_12563])).

tff(c_58,plain,(
    ! [C_73,A_71] :
      ( k1_xboole_0 = C_73
      | ~ v1_funct_2(C_73,A_71,k1_xboole_0)
      | k1_xboole_0 = A_71
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_71929,plain,(
    ! [C_5150,A_5151] :
      ( C_5150 = '#skF_9'
      | ~ v1_funct_2(C_5150,A_5151,'#skF_9')
      | A_5151 = '#skF_9'
      | ~ m1_subset_1(C_5150,k1_zfmisc_1(k2_zfmisc_1(A_5151,'#skF_9'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70955,c_70955,c_70955,c_70955,c_58])).

tff(c_71932,plain,
    ( '#skF_10' = '#skF_9'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
    | '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_70,c_71929])).

tff(c_71935,plain,
    ( '#skF_10' = '#skF_9'
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_71932])).

tff(c_71936,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_71935])).

tff(c_71980,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71936,c_72])).

tff(c_71979,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71936,c_70])).

tff(c_64,plain,(
    ! [B_72,C_73] :
      ( k1_relset_1(k1_xboole_0,B_72,C_73) = k1_xboole_0
      | ~ v1_funct_2(C_73,k1_xboole_0,B_72)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_71014,plain,(
    ! [B_72,C_73] :
      ( k1_relset_1('#skF_9',B_72,C_73) = '#skF_9'
      | ~ v1_funct_2(C_73,'#skF_9',B_72)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1('#skF_9',B_72))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70955,c_70955,c_70955,c_70955,c_64])).

tff(c_72064,plain,(
    ! [B_72,C_73] :
      ( k1_relset_1('#skF_8',B_72,C_73) = '#skF_8'
      | ~ v1_funct_2(C_73,'#skF_8',B_72)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1('#skF_8',B_72))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71936,c_71936,c_71936,c_71936,c_71014])).

tff(c_72076,plain,
    ( k1_relset_1('#skF_8','#skF_8','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_71979,c_72064])).

tff(c_72088,plain,(
    k1_relset_1('#skF_8','#skF_8','#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71980,c_72076])).

tff(c_71976,plain,(
    k1_relset_1('#skF_8','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71936,c_161])).

tff(c_72098,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72088,c_71976])).

tff(c_72100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70956,c_72098])).

tff(c_72101,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_71935])).

tff(c_72115,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72101,c_91])).

tff(c_72120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71017,c_72115])).

tff(c_72122,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_9747])).

tff(c_72184,plain,(
    ! [A_5156,B_5157] : ~ r2_hidden(A_5156,k9_relat_1(k1_xboole_0,B_5157)) ),
    inference(splitRight,[status(thm)],[c_9747])).

tff(c_72262,plain,(
    ! [B_5160] : k9_relat_1(k1_xboole_0,B_5160) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_276,c_72184])).

tff(c_72320,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_72262,c_28])).

tff(c_72360,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72122,c_72320])).

tff(c_138490,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138482,c_138482,c_72360])).

tff(c_138483,plain,(
    k1_relat_1('#skF_10') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_75615])).

tff(c_139418,plain,(
    ! [C_9347,A_9348] :
      ( C_9347 = '#skF_9'
      | ~ v1_funct_2(C_9347,A_9348,'#skF_9')
      | A_9348 = '#skF_9'
      | ~ m1_subset_1(C_9347,k1_zfmisc_1(k2_zfmisc_1(A_9348,'#skF_9'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138482,c_138482,c_138482,c_138482,c_58])).

tff(c_139421,plain,
    ( '#skF_10' = '#skF_9'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
    | '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_70,c_139418])).

tff(c_139424,plain,
    ( '#skF_10' = '#skF_9'
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_139421])).

tff(c_139425,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_139424])).

tff(c_139467,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139425,c_72])).

tff(c_139463,plain,(
    k1_relset_1('#skF_8','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139425,c_161])).

tff(c_139466,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139425,c_70])).

tff(c_138492,plain,(
    ! [B_72,C_73] :
      ( k1_relset_1('#skF_9',B_72,C_73) = '#skF_9'
      | ~ v1_funct_2(C_73,'#skF_9',B_72)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1('#skF_9',B_72))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138482,c_138482,c_138482,c_138482,c_64])).

tff(c_139602,plain,(
    ! [B_9355,C_9356] :
      ( k1_relset_1('#skF_8',B_9355,C_9356) = '#skF_8'
      | ~ v1_funct_2(C_9356,'#skF_8',B_9355)
      | ~ m1_subset_1(C_9356,k1_zfmisc_1(k2_zfmisc_1('#skF_8',B_9355))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139425,c_139425,c_139425,c_139425,c_138492])).

tff(c_139605,plain,
    ( k1_relset_1('#skF_8','#skF_8','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_139466,c_139602])).

tff(c_139608,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139467,c_139463,c_139605])).

tff(c_139610,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138483,c_139608])).

tff(c_139611,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_139424])).

tff(c_139618,plain,(
    k2_relat_1('#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139611,c_121])).

tff(c_139627,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138490,c_139618])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:57:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.35/15.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.42/15.92  
% 24.42/15.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.42/15.93  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_10 > #skF_9 > #skF_7 > #skF_8 > #skF_11 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 24.42/15.93  
% 24.42/15.93  %Foreground sorts:
% 24.42/15.93  
% 24.42/15.93  
% 24.42/15.93  %Background operators:
% 24.42/15.93  
% 24.42/15.93  
% 24.42/15.93  %Foreground operators:
% 24.42/15.93  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 24.42/15.93  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 24.42/15.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 24.42/15.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.42/15.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.42/15.93  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 24.42/15.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 24.42/15.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.42/15.93  tff('#skF_10', type, '#skF_10': $i).
% 24.42/15.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 24.42/15.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 24.42/15.93  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 24.42/15.93  tff('#skF_9', type, '#skF_9': $i).
% 24.42/15.93  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 24.42/15.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 24.42/15.93  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 24.42/15.93  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 24.42/15.93  tff('#skF_8', type, '#skF_8': $i).
% 24.42/15.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.42/15.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 24.42/15.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 24.42/15.93  tff('#skF_11', type, '#skF_11': $i > $i).
% 24.42/15.93  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 24.42/15.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.42/15.93  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 24.42/15.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 24.42/15.93  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 24.42/15.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 24.42/15.93  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 24.42/15.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 24.42/15.93  
% 24.57/15.95  tff(f_131, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 24.57/15.95  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 24.57/15.95  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 24.57/15.95  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 24.57/15.95  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 24.57/15.95  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 24.57/15.95  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 24.57/15.95  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 24.57/15.95  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 24.57/15.95  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 24.57/15.95  tff(f_40, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 24.57/15.95  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 24.57/15.95  tff(f_82, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 24.57/15.95  tff(c_70, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 24.57/15.95  tff(c_116, plain, (![A_100, B_101, C_102]: (k2_relset_1(A_100, B_101, C_102)=k2_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 24.57/15.95  tff(c_120, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_70, c_116])).
% 24.57/15.95  tff(c_68, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_131])).
% 24.57/15.95  tff(c_121, plain, (k2_relat_1('#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_68])).
% 24.57/15.95  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 24.57/15.95  tff(c_78, plain, (![D_77]: (r2_hidden('#skF_11'(D_77), '#skF_8') | ~r2_hidden(D_77, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 24.57/15.95  tff(c_72, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_131])).
% 24.57/15.95  tff(c_157, plain, (![A_112, B_113, C_114]: (k1_relset_1(A_112, B_113, C_114)=k1_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 24.57/15.95  tff(c_161, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_70, c_157])).
% 24.57/15.95  tff(c_75609, plain, (![B_5443, A_5444, C_5445]: (k1_xboole_0=B_5443 | k1_relset_1(A_5444, B_5443, C_5445)=A_5444 | ~v1_funct_2(C_5445, A_5444, B_5443) | ~m1_subset_1(C_5445, k1_zfmisc_1(k2_zfmisc_1(A_5444, B_5443))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 24.57/15.95  tff(c_75612, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_70, c_75609])).
% 24.57/15.95  tff(c_75615, plain, (k1_xboole_0='#skF_9' | k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_161, c_75612])).
% 24.57/15.95  tff(c_75616, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(splitLeft, [status(thm)], [c_75615])).
% 24.57/15.95  tff(c_87, plain, (![C_84, A_85, B_86]: (v1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 24.57/15.95  tff(c_91, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_70, c_87])).
% 24.57/15.95  tff(c_74, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_131])).
% 24.57/15.95  tff(c_76, plain, (![D_77]: (k1_funct_1('#skF_10', '#skF_11'(D_77))=D_77 | ~r2_hidden(D_77, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 24.57/15.95  tff(c_330, plain, (![A_155, D_156]: (r2_hidden(k1_funct_1(A_155, D_156), k2_relat_1(A_155)) | ~r2_hidden(D_156, k1_relat_1(A_155)) | ~v1_funct_1(A_155) | ~v1_relat_1(A_155))), inference(cnfTransformation, [status(thm)], [f_77])).
% 24.57/15.95  tff(c_338, plain, (![D_77]: (r2_hidden(D_77, k2_relat_1('#skF_10')) | ~r2_hidden('#skF_11'(D_77), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(D_77, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_330])).
% 24.57/15.95  tff(c_342, plain, (![D_77]: (r2_hidden(D_77, k2_relat_1('#skF_10')) | ~r2_hidden('#skF_11'(D_77), k1_relat_1('#skF_10')) | ~r2_hidden(D_77, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_74, c_338])).
% 24.57/15.95  tff(c_75653, plain, (![D_5446]: (r2_hidden(D_5446, k2_relat_1('#skF_10')) | ~r2_hidden('#skF_11'(D_5446), '#skF_8') | ~r2_hidden(D_5446, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_75616, c_342])).
% 24.57/15.95  tff(c_75662, plain, (![D_77]: (r2_hidden(D_77, k2_relat_1('#skF_10')) | ~r2_hidden(D_77, '#skF_9'))), inference(resolution, [status(thm)], [c_78, c_75653])).
% 24.57/15.95  tff(c_167, plain, (![A_117, B_118]: (r2_hidden('#skF_1'(A_117, B_118), B_118) | r2_hidden('#skF_2'(A_117, B_118), A_117) | B_118=A_117)), inference(cnfTransformation, [status(thm)], [f_32])).
% 24.57/15.95  tff(c_18, plain, (![C_12, A_9, B_10]: (r2_hidden(C_12, A_9) | ~r2_hidden(C_12, B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 24.57/15.95  tff(c_77261, plain, (![A_5570, B_5571, A_5572]: (r2_hidden('#skF_2'(A_5570, B_5571), A_5572) | ~m1_subset_1(A_5570, k1_zfmisc_1(A_5572)) | r2_hidden('#skF_1'(A_5570, B_5571), B_5571) | B_5571=A_5570)), inference(resolution, [status(thm)], [c_167, c_18])).
% 24.57/15.95  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 24.57/15.95  tff(c_77384, plain, (![A_5573, A_5574]: (~m1_subset_1(A_5573, k1_zfmisc_1(A_5574)) | r2_hidden('#skF_1'(A_5573, A_5574), A_5574) | A_5574=A_5573)), inference(resolution, [status(thm)], [c_77261, c_4])).
% 24.57/15.95  tff(c_77541, plain, (![A_5584, A_5585, A_5586]: (r2_hidden('#skF_1'(A_5584, A_5585), A_5586) | ~m1_subset_1(A_5585, k1_zfmisc_1(A_5586)) | ~m1_subset_1(A_5584, k1_zfmisc_1(A_5585)) | A_5585=A_5584)), inference(resolution, [status(thm)], [c_77384, c_18])).
% 24.57/15.95  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 24.57/15.95  tff(c_77638, plain, (![A_5600, A_5601]: (~r2_hidden('#skF_2'(A_5600, A_5601), A_5601) | ~m1_subset_1(A_5601, k1_zfmisc_1(A_5600)) | ~m1_subset_1(A_5600, k1_zfmisc_1(A_5601)) | A_5601=A_5600)), inference(resolution, [status(thm)], [c_77541, c_2])).
% 24.57/15.95  tff(c_85478, plain, (![A_6077]: (~m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1(A_6077)) | ~m1_subset_1(A_6077, k1_zfmisc_1(k2_relat_1('#skF_10'))) | k2_relat_1('#skF_10')=A_6077 | ~r2_hidden('#skF_2'(A_6077, k2_relat_1('#skF_10')), '#skF_9'))), inference(resolution, [status(thm)], [c_75662, c_77638])).
% 24.57/15.95  tff(c_85498, plain, (~m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1('#skF_9')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_relat_1('#skF_10'))) | ~r2_hidden('#skF_1'('#skF_9', k2_relat_1('#skF_10')), '#skF_9') | k2_relat_1('#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_6, c_85478])).
% 24.57/15.95  tff(c_85508, plain, (~m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1('#skF_9')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_relat_1('#skF_10'))) | ~r2_hidden('#skF_1'('#skF_9', k2_relat_1('#skF_10')), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_121, c_121, c_85498])).
% 24.57/15.95  tff(c_85782, plain, (~r2_hidden('#skF_1'('#skF_9', k2_relat_1('#skF_10')), '#skF_9')), inference(splitLeft, [status(thm)], [c_85508])).
% 24.57/15.95  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 24.57/15.95  tff(c_28, plain, (![A_19]: (k9_relat_1(A_19, k1_relat_1(A_19))=k2_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 24.57/15.95  tff(c_9720, plain, (![A_1018, B_1019, C_1020]: (r2_hidden(k4_tarski('#skF_3'(A_1018, B_1019, C_1020), A_1018), C_1020) | ~r2_hidden(A_1018, k9_relat_1(C_1020, B_1019)) | ~v1_relat_1(C_1020))), inference(cnfTransformation, [status(thm)], [f_58])).
% 24.57/15.95  tff(c_94133, plain, (![A_6589, B_6590, C_6591, A_6592]: (r2_hidden(k4_tarski('#skF_3'(A_6589, B_6590, C_6591), A_6589), A_6592) | ~m1_subset_1(C_6591, k1_zfmisc_1(A_6592)) | ~r2_hidden(A_6589, k9_relat_1(C_6591, B_6590)) | ~v1_relat_1(C_6591))), inference(resolution, [status(thm)], [c_9720, c_18])).
% 24.57/15.95  tff(c_14, plain, (![B_6, D_8, A_5, C_7]: (r2_hidden(B_6, D_8) | ~r2_hidden(k4_tarski(A_5, B_6), k2_zfmisc_1(C_7, D_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 24.57/15.95  tff(c_134430, plain, (![C_9106, D_9104, B_9108, C_9107, A_9105]: (r2_hidden(A_9105, D_9104) | ~m1_subset_1(C_9106, k1_zfmisc_1(k2_zfmisc_1(C_9107, D_9104))) | ~r2_hidden(A_9105, k9_relat_1(C_9106, B_9108)) | ~v1_relat_1(C_9106))), inference(resolution, [status(thm)], [c_94133, c_14])).
% 24.57/15.95  tff(c_134432, plain, (![A_9105, B_9108]: (r2_hidden(A_9105, '#skF_9') | ~r2_hidden(A_9105, k9_relat_1('#skF_10', B_9108)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_70, c_134430])).
% 24.57/15.95  tff(c_134436, plain, (![A_9109, B_9110]: (r2_hidden(A_9109, '#skF_9') | ~r2_hidden(A_9109, k9_relat_1('#skF_10', B_9110)))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_134432])).
% 24.57/15.95  tff(c_134616, plain, (![A_9109]: (r2_hidden(A_9109, '#skF_9') | ~r2_hidden(A_9109, k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_134436])).
% 24.57/15.95  tff(c_134689, plain, (![A_9113]: (r2_hidden(A_9113, '#skF_9') | ~r2_hidden(A_9113, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_134616])).
% 24.57/15.95  tff(c_134902, plain, (![A_1]: (r2_hidden('#skF_1'(A_1, k2_relat_1('#skF_10')), '#skF_9') | r2_hidden('#skF_2'(A_1, k2_relat_1('#skF_10')), A_1) | k2_relat_1('#skF_10')=A_1)), inference(resolution, [status(thm)], [c_8, c_134689])).
% 24.57/15.95  tff(c_75663, plain, (![D_5447]: (r2_hidden(D_5447, k2_relat_1('#skF_10')) | ~r2_hidden(D_5447, '#skF_9'))), inference(resolution, [status(thm)], [c_78, c_75653])).
% 24.57/15.95  tff(c_75682, plain, (![A_1]: (r2_hidden('#skF_1'(A_1, k2_relat_1('#skF_10')), k2_relat_1('#skF_10')) | k2_relat_1('#skF_10')=A_1 | ~r2_hidden('#skF_2'(A_1, k2_relat_1('#skF_10')), '#skF_9'))), inference(resolution, [status(thm)], [c_75663, c_4])).
% 24.57/15.95  tff(c_138370, plain, (![A_9279]: (r2_hidden('#skF_1'(A_9279, k2_relat_1('#skF_10')), '#skF_9') | k2_relat_1('#skF_10')=A_9279 | ~r2_hidden('#skF_2'(A_9279, k2_relat_1('#skF_10')), '#skF_9'))), inference(resolution, [status(thm)], [c_75682, c_134689])).
% 24.57/15.95  tff(c_138376, plain, (r2_hidden('#skF_1'('#skF_9', k2_relat_1('#skF_10')), '#skF_9') | k2_relat_1('#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_134902, c_138370])).
% 24.57/15.95  tff(c_138412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_85782, c_121, c_85782, c_138376])).
% 24.57/15.95  tff(c_138414, plain, (r2_hidden('#skF_1'('#skF_9', k2_relat_1('#skF_10')), '#skF_9')), inference(splitRight, [status(thm)], [c_85508])).
% 24.57/15.95  tff(c_138423, plain, (~r2_hidden('#skF_2'('#skF_9', k2_relat_1('#skF_10')), k2_relat_1('#skF_10')) | k2_relat_1('#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_138414, c_2])).
% 24.57/15.95  tff(c_138438, plain, (~r2_hidden('#skF_2'('#skF_9', k2_relat_1('#skF_10')), k2_relat_1('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_121, c_138423])).
% 24.57/15.95  tff(c_138455, plain, (~r2_hidden('#skF_2'('#skF_9', k2_relat_1('#skF_10')), '#skF_9')), inference(resolution, [status(thm)], [c_75662, c_138438])).
% 24.57/15.95  tff(c_138469, plain, (~r2_hidden('#skF_1'('#skF_9', k2_relat_1('#skF_10')), '#skF_9') | k2_relat_1('#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_6, c_138455])).
% 24.57/15.95  tff(c_138479, plain, (k2_relat_1('#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_138414, c_138469])).
% 24.57/15.95  tff(c_138481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_138479])).
% 24.57/15.95  tff(c_138482, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_75615])).
% 24.57/15.95  tff(c_12557, plain, (![B_1299, A_1300, C_1301]: (k1_xboole_0=B_1299 | k1_relset_1(A_1300, B_1299, C_1301)=A_1300 | ~v1_funct_2(C_1301, A_1300, B_1299) | ~m1_subset_1(C_1301, k1_zfmisc_1(k2_zfmisc_1(A_1300, B_1299))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 24.57/15.95  tff(c_12560, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_70, c_12557])).
% 24.57/15.95  tff(c_12563, plain, (k1_xboole_0='#skF_9' | k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_161, c_12560])).
% 24.57/15.95  tff(c_12564, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(splitLeft, [status(thm)], [c_12563])).
% 24.57/15.95  tff(c_12602, plain, (![D_1304]: (r2_hidden(D_1304, k2_relat_1('#skF_10')) | ~r2_hidden('#skF_11'(D_1304), '#skF_8') | ~r2_hidden(D_1304, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_12564, c_342])).
% 24.57/15.95  tff(c_12611, plain, (![D_77]: (r2_hidden(D_77, k2_relat_1('#skF_10')) | ~r2_hidden(D_77, '#skF_9'))), inference(resolution, [status(thm)], [c_78, c_12602])).
% 24.57/15.95  tff(c_12275, plain, (![A_1273, B_1274, A_1275]: (r2_hidden('#skF_2'(A_1273, B_1274), A_1275) | ~m1_subset_1(A_1273, k1_zfmisc_1(A_1275)) | r2_hidden('#skF_1'(A_1273, B_1274), B_1274) | B_1274=A_1273)), inference(resolution, [status(thm)], [c_167, c_18])).
% 24.57/15.95  tff(c_12373, plain, (![A_1279, A_1280]: (~m1_subset_1(A_1279, k1_zfmisc_1(A_1280)) | r2_hidden('#skF_1'(A_1279, A_1280), A_1280) | A_1280=A_1279)), inference(resolution, [status(thm)], [c_12275, c_4])).
% 24.57/15.95  tff(c_12506, plain, (![A_1296, A_1297, A_1298]: (r2_hidden('#skF_1'(A_1296, A_1297), A_1298) | ~m1_subset_1(A_1297, k1_zfmisc_1(A_1298)) | ~m1_subset_1(A_1296, k1_zfmisc_1(A_1297)) | A_1297=A_1296)), inference(resolution, [status(thm)], [c_12373, c_18])).
% 24.57/15.95  tff(c_13731, plain, (![A_1362, A_1363]: (~r2_hidden('#skF_2'(A_1362, A_1363), A_1363) | ~m1_subset_1(A_1363, k1_zfmisc_1(A_1362)) | ~m1_subset_1(A_1362, k1_zfmisc_1(A_1363)) | A_1363=A_1362)), inference(resolution, [status(thm)], [c_12506, c_2])).
% 24.57/15.95  tff(c_21917, plain, (![A_1934]: (~m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1(A_1934)) | ~m1_subset_1(A_1934, k1_zfmisc_1(k2_relat_1('#skF_10'))) | k2_relat_1('#skF_10')=A_1934 | ~r2_hidden('#skF_2'(A_1934, k2_relat_1('#skF_10')), '#skF_9'))), inference(resolution, [status(thm)], [c_12611, c_13731])).
% 24.57/15.95  tff(c_21937, plain, (~m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1('#skF_9')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_relat_1('#skF_10'))) | ~r2_hidden('#skF_1'('#skF_9', k2_relat_1('#skF_10')), '#skF_9') | k2_relat_1('#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_6, c_21917])).
% 24.57/15.95  tff(c_21947, plain, (~m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1('#skF_9')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_relat_1('#skF_10'))) | ~r2_hidden('#skF_1'('#skF_9', k2_relat_1('#skF_10')), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_121, c_121, c_21937])).
% 24.57/15.95  tff(c_22158, plain, (~r2_hidden('#skF_1'('#skF_9', k2_relat_1('#skF_10')), '#skF_9')), inference(splitLeft, [status(thm)], [c_21947])).
% 24.57/15.95  tff(c_26060, plain, (![A_2222, B_2223, C_2224, A_2225]: (r2_hidden(k4_tarski('#skF_3'(A_2222, B_2223, C_2224), A_2222), A_2225) | ~m1_subset_1(C_2224, k1_zfmisc_1(A_2225)) | ~r2_hidden(A_2222, k9_relat_1(C_2224, B_2223)) | ~v1_relat_1(C_2224))), inference(resolution, [status(thm)], [c_9720, c_18])).
% 24.57/15.95  tff(c_66144, plain, (![B_4890, A_4891, D_4888, C_4887, C_4889]: (r2_hidden(A_4891, D_4888) | ~m1_subset_1(C_4887, k1_zfmisc_1(k2_zfmisc_1(C_4889, D_4888))) | ~r2_hidden(A_4891, k9_relat_1(C_4887, B_4890)) | ~v1_relat_1(C_4887))), inference(resolution, [status(thm)], [c_26060, c_14])).
% 24.57/15.95  tff(c_66146, plain, (![A_4891, B_4890]: (r2_hidden(A_4891, '#skF_9') | ~r2_hidden(A_4891, k9_relat_1('#skF_10', B_4890)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_70, c_66144])).
% 24.57/15.95  tff(c_66150, plain, (![A_4892, B_4893]: (r2_hidden(A_4892, '#skF_9') | ~r2_hidden(A_4892, k9_relat_1('#skF_10', B_4893)))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_66146])).
% 24.57/15.95  tff(c_66334, plain, (![A_4892]: (r2_hidden(A_4892, '#skF_9') | ~r2_hidden(A_4892, k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_66150])).
% 24.57/15.95  tff(c_66386, plain, (![A_4894]: (r2_hidden(A_4894, '#skF_9') | ~r2_hidden(A_4894, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_66334])).
% 24.57/15.95  tff(c_66599, plain, (![A_1]: (r2_hidden('#skF_1'(A_1, k2_relat_1('#skF_10')), '#skF_9') | r2_hidden('#skF_2'(A_1, k2_relat_1('#skF_10')), A_1) | k2_relat_1('#skF_10')=A_1)), inference(resolution, [status(thm)], [c_8, c_66386])).
% 24.57/15.95  tff(c_12612, plain, (![D_1305]: (r2_hidden(D_1305, k2_relat_1('#skF_10')) | ~r2_hidden(D_1305, '#skF_9'))), inference(resolution, [status(thm)], [c_78, c_12602])).
% 24.57/15.95  tff(c_12635, plain, (![A_1]: (r2_hidden('#skF_1'(A_1, k2_relat_1('#skF_10')), k2_relat_1('#skF_10')) | k2_relat_1('#skF_10')=A_1 | ~r2_hidden('#skF_2'(A_1, k2_relat_1('#skF_10')), '#skF_9'))), inference(resolution, [status(thm)], [c_12612, c_4])).
% 24.57/15.95  tff(c_70319, plain, (![A_5062]: (r2_hidden('#skF_1'(A_5062, k2_relat_1('#skF_10')), '#skF_9') | k2_relat_1('#skF_10')=A_5062 | ~r2_hidden('#skF_2'(A_5062, k2_relat_1('#skF_10')), '#skF_9'))), inference(resolution, [status(thm)], [c_12635, c_66386])).
% 24.57/15.95  tff(c_70325, plain, (r2_hidden('#skF_1'('#skF_9', k2_relat_1('#skF_10')), '#skF_9') | k2_relat_1('#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_66599, c_70319])).
% 24.57/15.95  tff(c_70361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_22158, c_121, c_22158, c_70325])).
% 24.57/15.95  tff(c_70363, plain, (r2_hidden('#skF_1'('#skF_9', k2_relat_1('#skF_10')), '#skF_9')), inference(splitRight, [status(thm)], [c_21947])).
% 24.57/15.95  tff(c_70896, plain, (~r2_hidden('#skF_2'('#skF_9', k2_relat_1('#skF_10')), k2_relat_1('#skF_10')) | k2_relat_1('#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_70363, c_2])).
% 24.57/15.95  tff(c_70911, plain, (~r2_hidden('#skF_2'('#skF_9', k2_relat_1('#skF_10')), k2_relat_1('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_121, c_70896])).
% 24.57/15.95  tff(c_70925, plain, (~r2_hidden('#skF_2'('#skF_9', k2_relat_1('#skF_10')), '#skF_9')), inference(resolution, [status(thm)], [c_12611, c_70911])).
% 24.57/15.95  tff(c_70942, plain, (~r2_hidden('#skF_1'('#skF_9', k2_relat_1('#skF_10')), '#skF_9') | k2_relat_1('#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_6, c_70925])).
% 24.57/15.95  tff(c_70952, plain, (k2_relat_1('#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_70363, c_70942])).
% 24.57/15.95  tff(c_70954, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_70952])).
% 24.57/15.95  tff(c_70955, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_12563])).
% 24.57/15.95  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 24.57/15.95  tff(c_48, plain, (![B_61, A_60]: (~r1_tarski(B_61, A_60) | ~r2_hidden(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_82])).
% 24.57/15.95  tff(c_272, plain, (![B_137, A_138]: (~r1_tarski(B_137, '#skF_1'(A_138, B_137)) | r2_hidden('#skF_2'(A_138, B_137), A_138) | B_137=A_138)), inference(resolution, [status(thm)], [c_167, c_48])).
% 24.57/15.95  tff(c_276, plain, (![A_138]: (r2_hidden('#skF_2'(A_138, k1_xboole_0), A_138) | k1_xboole_0=A_138)), inference(resolution, [status(thm)], [c_10, c_272])).
% 24.57/15.95  tff(c_310, plain, (![A_143, B_144, C_145]: (r2_hidden('#skF_3'(A_143, B_144, C_145), B_144) | ~r2_hidden(A_143, k9_relat_1(C_145, B_144)) | ~v1_relat_1(C_145))), inference(cnfTransformation, [status(thm)], [f_58])).
% 24.57/15.95  tff(c_325, plain, (![B_152, A_153, C_154]: (~r1_tarski(B_152, '#skF_3'(A_153, B_152, C_154)) | ~r2_hidden(A_153, k9_relat_1(C_154, B_152)) | ~v1_relat_1(C_154))), inference(resolution, [status(thm)], [c_310, c_48])).
% 24.57/15.95  tff(c_343, plain, (![A_157, C_158]: (~r2_hidden(A_157, k9_relat_1(C_158, k1_xboole_0)) | ~v1_relat_1(C_158))), inference(resolution, [status(thm)], [c_10, c_325])).
% 24.57/15.95  tff(c_389, plain, (![C_159]: (~v1_relat_1(C_159) | k9_relat_1(C_159, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_276, c_343])).
% 24.57/15.95  tff(c_393, plain, (k9_relat_1('#skF_10', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_91, c_389])).
% 24.57/15.95  tff(c_329, plain, (![A_153, C_154]: (~r2_hidden(A_153, k9_relat_1(C_154, k1_xboole_0)) | ~v1_relat_1(C_154))), inference(resolution, [status(thm)], [c_10, c_325])).
% 24.57/15.95  tff(c_397, plain, (![A_153]: (~r2_hidden(A_153, k1_xboole_0) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_393, c_329])).
% 24.57/15.95  tff(c_401, plain, (![A_153]: (~r2_hidden(A_153, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_397])).
% 24.57/15.95  tff(c_9747, plain, (![A_1018, B_1019]: (~r2_hidden(A_1018, k9_relat_1(k1_xboole_0, B_1019)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_9720, c_401])).
% 24.57/15.95  tff(c_9753, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_9747])).
% 24.57/15.95  tff(c_71017, plain, (~v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_70955, c_9753])).
% 24.57/15.95  tff(c_70956, plain, (k1_relat_1('#skF_10')!='#skF_8'), inference(splitRight, [status(thm)], [c_12563])).
% 24.57/15.95  tff(c_58, plain, (![C_73, A_71]: (k1_xboole_0=C_73 | ~v1_funct_2(C_73, A_71, k1_xboole_0) | k1_xboole_0=A_71 | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 24.57/15.95  tff(c_71929, plain, (![C_5150, A_5151]: (C_5150='#skF_9' | ~v1_funct_2(C_5150, A_5151, '#skF_9') | A_5151='#skF_9' | ~m1_subset_1(C_5150, k1_zfmisc_1(k2_zfmisc_1(A_5151, '#skF_9'))))), inference(demodulation, [status(thm), theory('equality')], [c_70955, c_70955, c_70955, c_70955, c_58])).
% 24.57/15.95  tff(c_71932, plain, ('#skF_10'='#skF_9' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | '#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_70, c_71929])).
% 24.57/15.95  tff(c_71935, plain, ('#skF_10'='#skF_9' | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_71932])).
% 24.57/15.95  tff(c_71936, plain, ('#skF_9'='#skF_8'), inference(splitLeft, [status(thm)], [c_71935])).
% 24.57/15.95  tff(c_71980, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_71936, c_72])).
% 24.57/15.95  tff(c_71979, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_71936, c_70])).
% 24.57/15.95  tff(c_64, plain, (![B_72, C_73]: (k1_relset_1(k1_xboole_0, B_72, C_73)=k1_xboole_0 | ~v1_funct_2(C_73, k1_xboole_0, B_72) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_72))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 24.57/15.95  tff(c_71014, plain, (![B_72, C_73]: (k1_relset_1('#skF_9', B_72, C_73)='#skF_9' | ~v1_funct_2(C_73, '#skF_9', B_72) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1('#skF_9', B_72))))), inference(demodulation, [status(thm), theory('equality')], [c_70955, c_70955, c_70955, c_70955, c_64])).
% 24.57/15.95  tff(c_72064, plain, (![B_72, C_73]: (k1_relset_1('#skF_8', B_72, C_73)='#skF_8' | ~v1_funct_2(C_73, '#skF_8', B_72) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1('#skF_8', B_72))))), inference(demodulation, [status(thm), theory('equality')], [c_71936, c_71936, c_71936, c_71936, c_71014])).
% 24.57/15.95  tff(c_72076, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_71979, c_72064])).
% 24.57/15.95  tff(c_72088, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_71980, c_72076])).
% 24.57/15.95  tff(c_71976, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_71936, c_161])).
% 24.57/15.95  tff(c_72098, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_72088, c_71976])).
% 24.57/15.95  tff(c_72100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70956, c_72098])).
% 24.57/15.95  tff(c_72101, plain, ('#skF_10'='#skF_9'), inference(splitRight, [status(thm)], [c_71935])).
% 24.57/15.95  tff(c_72115, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_72101, c_91])).
% 24.57/15.95  tff(c_72120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71017, c_72115])).
% 24.57/15.95  tff(c_72122, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_9747])).
% 24.57/15.95  tff(c_72184, plain, (![A_5156, B_5157]: (~r2_hidden(A_5156, k9_relat_1(k1_xboole_0, B_5157)))), inference(splitRight, [status(thm)], [c_9747])).
% 24.57/15.95  tff(c_72262, plain, (![B_5160]: (k9_relat_1(k1_xboole_0, B_5160)=k1_xboole_0)), inference(resolution, [status(thm)], [c_276, c_72184])).
% 24.57/15.95  tff(c_72320, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_72262, c_28])).
% 24.57/15.95  tff(c_72360, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_72122, c_72320])).
% 24.57/15.95  tff(c_138490, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_138482, c_138482, c_72360])).
% 24.57/15.95  tff(c_138483, plain, (k1_relat_1('#skF_10')!='#skF_8'), inference(splitRight, [status(thm)], [c_75615])).
% 24.57/15.95  tff(c_139418, plain, (![C_9347, A_9348]: (C_9347='#skF_9' | ~v1_funct_2(C_9347, A_9348, '#skF_9') | A_9348='#skF_9' | ~m1_subset_1(C_9347, k1_zfmisc_1(k2_zfmisc_1(A_9348, '#skF_9'))))), inference(demodulation, [status(thm), theory('equality')], [c_138482, c_138482, c_138482, c_138482, c_58])).
% 24.57/15.95  tff(c_139421, plain, ('#skF_10'='#skF_9' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | '#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_70, c_139418])).
% 24.57/15.95  tff(c_139424, plain, ('#skF_10'='#skF_9' | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_139421])).
% 24.57/15.95  tff(c_139425, plain, ('#skF_9'='#skF_8'), inference(splitLeft, [status(thm)], [c_139424])).
% 24.57/15.95  tff(c_139467, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_139425, c_72])).
% 24.57/15.95  tff(c_139463, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_139425, c_161])).
% 24.57/15.95  tff(c_139466, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_139425, c_70])).
% 24.57/15.95  tff(c_138492, plain, (![B_72, C_73]: (k1_relset_1('#skF_9', B_72, C_73)='#skF_9' | ~v1_funct_2(C_73, '#skF_9', B_72) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1('#skF_9', B_72))))), inference(demodulation, [status(thm), theory('equality')], [c_138482, c_138482, c_138482, c_138482, c_64])).
% 24.57/15.95  tff(c_139602, plain, (![B_9355, C_9356]: (k1_relset_1('#skF_8', B_9355, C_9356)='#skF_8' | ~v1_funct_2(C_9356, '#skF_8', B_9355) | ~m1_subset_1(C_9356, k1_zfmisc_1(k2_zfmisc_1('#skF_8', B_9355))))), inference(demodulation, [status(thm), theory('equality')], [c_139425, c_139425, c_139425, c_139425, c_138492])).
% 24.57/15.95  tff(c_139605, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_139466, c_139602])).
% 24.57/15.95  tff(c_139608, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_139467, c_139463, c_139605])).
% 24.57/15.95  tff(c_139610, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138483, c_139608])).
% 24.57/15.95  tff(c_139611, plain, ('#skF_10'='#skF_9'), inference(splitRight, [status(thm)], [c_139424])).
% 24.57/15.95  tff(c_139618, plain, (k2_relat_1('#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_139611, c_121])).
% 24.57/15.95  tff(c_139627, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138490, c_139618])).
% 24.57/15.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.57/15.95  
% 24.57/15.95  Inference rules
% 24.57/15.95  ----------------------
% 24.57/15.95  #Ref     : 52
% 24.57/15.95  #Sup     : 27018
% 24.57/15.95  #Fact    : 0
% 24.57/15.95  #Define  : 0
% 24.57/15.95  #Split   : 106
% 24.57/15.95  #Chain   : 0
% 24.57/15.95  #Close   : 0
% 24.57/15.95  
% 24.57/15.95  Ordering : KBO
% 24.57/15.95  
% 24.57/15.95  Simplification rules
% 24.57/15.95  ----------------------
% 24.57/15.95  #Subsume      : 11291
% 24.57/15.95  #Demod        : 17966
% 24.57/15.95  #Tautology    : 1837
% 24.57/15.95  #SimpNegUnit  : 844
% 24.57/15.95  #BackRed      : 6409
% 24.57/15.95  
% 24.57/15.95  #Partial instantiations: 0
% 24.57/15.95  #Strategies tried      : 1
% 24.57/15.95  
% 24.57/15.95  Timing (in seconds)
% 24.57/15.95  ----------------------
% 24.57/15.95  Preprocessing        : 0.35
% 24.57/15.95  Parsing              : 0.18
% 24.57/15.96  CNF conversion       : 0.03
% 24.57/15.96  Main loop            : 14.80
% 24.57/15.96  Inferencing          : 3.64
% 24.57/15.96  Reduction            : 4.13
% 24.57/15.96  Demodulation         : 2.67
% 24.57/15.96  BG Simplification    : 0.38
% 24.57/15.96  Subsumption          : 5.08
% 24.57/15.96  Abstraction          : 0.53
% 24.57/15.96  MUC search           : 0.00
% 24.57/15.96  Cooper               : 0.00
% 24.57/15.96  Total                : 15.21
% 24.57/15.96  Index Insertion      : 0.00
% 24.57/15.96  Index Deletion       : 0.00
% 24.57/15.96  Index Matching       : 0.00
% 24.57/15.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
