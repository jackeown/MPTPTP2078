%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:28 EST 2020

% Result     : Theorem 8.06s
% Output     : CNFRefutation 8.06s
% Verified   : 
% Statistics : Number of formulae       :  150 (2877 expanded)
%              Number of leaves         :   44 (1013 expanded)
%              Depth                    :   17
%              Number of atoms          :  285 (9712 expanded)
%              Number of equality atoms :   68 (4173 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_15 > #skF_14 > #skF_13 > #skF_5 > #skF_11 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_12 > #skF_4 > #skF_10

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_15',type,(
    '#skF_15': $i > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_121,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_82,axiom,(
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

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
      <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_72,plain,(
    k2_relset_1('#skF_12','#skF_13','#skF_14') != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_101,plain,(
    ! [A_110,B_111] :
      ( r2_hidden('#skF_1'(A_110,B_111),A_110)
      | r1_tarski(A_110,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,(
    ! [A_110] : r1_tarski(A_110,A_110) ),
    inference(resolution,[status(thm)],[c_101,c_4])).

tff(c_74,plain,(
    m1_subset_1('#skF_14',k1_zfmisc_1(k2_zfmisc_1('#skF_12','#skF_13'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    v1_funct_2('#skF_14','#skF_12','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_166,plain,(
    ! [A_137,B_138,C_139] :
      ( k1_relset_1(A_137,B_138,C_139) = k1_relat_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_170,plain,(
    k1_relset_1('#skF_12','#skF_13','#skF_14') = k1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_74,c_166])).

tff(c_772,plain,(
    ! [B_243,A_244,C_245] :
      ( k1_xboole_0 = B_243
      | k1_relset_1(A_244,B_243,C_245) = A_244
      | ~ v1_funct_2(C_245,A_244,B_243)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(A_244,B_243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_775,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_relset_1('#skF_12','#skF_13','#skF_14') = '#skF_12'
    | ~ v1_funct_2('#skF_14','#skF_12','#skF_13') ),
    inference(resolution,[status(thm)],[c_74,c_772])).

tff(c_778,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_relat_1('#skF_14') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_170,c_775])).

tff(c_779,plain,(
    k1_relat_1('#skF_14') = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_778])).

tff(c_82,plain,(
    ! [D_99] :
      ( r2_hidden('#skF_15'(D_99),'#skF_12')
      | ~ r2_hidden(D_99,'#skF_13') ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_121,plain,(
    ! [C_120,B_121,A_122] :
      ( r2_hidden(C_120,B_121)
      | ~ r2_hidden(C_120,A_122)
      | ~ r1_tarski(A_122,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_127,plain,(
    ! [D_99,B_121] :
      ( r2_hidden('#skF_15'(D_99),B_121)
      | ~ r1_tarski('#skF_12',B_121)
      | ~ r2_hidden(D_99,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_82,c_121])).

tff(c_22,plain,(
    ! [A_28,B_29] : v1_relat_1(k2_zfmisc_1(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_112,plain,(
    ! [B_113,A_114] :
      ( v1_relat_1(B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_114))
      | ~ v1_relat_1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_115,plain,
    ( v1_relat_1('#skF_14')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_12','#skF_13')) ),
    inference(resolution,[status(thm)],[c_74,c_112])).

tff(c_118,plain,(
    v1_relat_1('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_115])).

tff(c_78,plain,(
    v1_funct_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_80,plain,(
    ! [D_99] :
      ( k1_funct_1('#skF_14','#skF_15'(D_99)) = D_99
      | ~ r2_hidden(D_99,'#skF_13') ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_227,plain,(
    ! [A_151,D_152] :
      ( r2_hidden(k1_funct_1(A_151,D_152),k2_relat_1(A_151))
      | ~ r2_hidden(D_152,k1_relat_1(A_151))
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_238,plain,(
    ! [D_99] :
      ( r2_hidden(D_99,k2_relat_1('#skF_14'))
      | ~ r2_hidden('#skF_15'(D_99),k1_relat_1('#skF_14'))
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14')
      | ~ r2_hidden(D_99,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_227])).

tff(c_243,plain,(
    ! [D_153] :
      ( r2_hidden(D_153,k2_relat_1('#skF_14'))
      | ~ r2_hidden('#skF_15'(D_153),k1_relat_1('#skF_14'))
      | ~ r2_hidden(D_153,'#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_78,c_238])).

tff(c_254,plain,(
    ! [D_99] :
      ( r2_hidden(D_99,k2_relat_1('#skF_14'))
      | ~ r1_tarski('#skF_12',k1_relat_1('#skF_14'))
      | ~ r2_hidden(D_99,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_127,c_243])).

tff(c_255,plain,(
    ~ r1_tarski('#skF_12',k1_relat_1('#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_801,plain,(
    ~ r1_tarski('#skF_12','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_255])).

tff(c_806,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_801])).

tff(c_808,plain,(
    k1_relat_1('#skF_14') != '#skF_12' ),
    inference(splitRight,[status(thm)],[c_778])).

tff(c_807,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_778])).

tff(c_62,plain,(
    ! [C_95,A_93] :
      ( k1_xboole_0 = C_95
      | ~ v1_funct_2(C_95,A_93,k1_xboole_0)
      | k1_xboole_0 = A_93
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1032,plain,(
    ! [C_262,A_263] :
      ( C_262 = '#skF_13'
      | ~ v1_funct_2(C_262,A_263,'#skF_13')
      | A_263 = '#skF_13'
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_263,'#skF_13'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_807,c_807,c_807,c_807,c_62])).

tff(c_1035,plain,
    ( '#skF_14' = '#skF_13'
    | ~ v1_funct_2('#skF_14','#skF_12','#skF_13')
    | '#skF_13' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_74,c_1032])).

tff(c_1038,plain,
    ( '#skF_14' = '#skF_13'
    | '#skF_13' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1035])).

tff(c_1039,plain,(
    '#skF_13' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_1038])).

tff(c_1098,plain,(
    v1_funct_2('#skF_14','#skF_12','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1039,c_76])).

tff(c_1089,plain,(
    k1_relset_1('#skF_12','#skF_12','#skF_14') = k1_relat_1('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1039,c_170])).

tff(c_1096,plain,(
    m1_subset_1('#skF_14',k1_zfmisc_1(k2_zfmisc_1('#skF_12','#skF_12'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1039,c_74])).

tff(c_68,plain,(
    ! [B_94,C_95] :
      ( k1_relset_1(k1_xboole_0,B_94,C_95) = k1_xboole_0
      | ~ v1_funct_2(C_95,k1_xboole_0,B_94)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_821,plain,(
    ! [B_94,C_95] :
      ( k1_relset_1('#skF_13',B_94,C_95) = '#skF_13'
      | ~ v1_funct_2(C_95,'#skF_13',B_94)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1('#skF_13',B_94))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_807,c_807,c_807,c_807,c_68])).

tff(c_1624,plain,(
    ! [B_318,C_319] :
      ( k1_relset_1('#skF_12',B_318,C_319) = '#skF_12'
      | ~ v1_funct_2(C_319,'#skF_12',B_318)
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1('#skF_12',B_318))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1039,c_1039,c_1039,c_1039,c_821])).

tff(c_1627,plain,
    ( k1_relset_1('#skF_12','#skF_12','#skF_14') = '#skF_12'
    | ~ v1_funct_2('#skF_14','#skF_12','#skF_12') ),
    inference(resolution,[status(thm)],[c_1096,c_1624])).

tff(c_1630,plain,(
    k1_relat_1('#skF_14') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1098,c_1089,c_1627])).

tff(c_1632,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_808,c_1630])).

tff(c_1633,plain,(
    '#skF_14' = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_1038])).

tff(c_1683,plain,(
    k2_relset_1('#skF_12','#skF_13','#skF_13') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1633,c_72])).

tff(c_1682,plain,(
    m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_12','#skF_13'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1633,c_74])).

tff(c_698,plain,(
    ! [A_228,B_229,C_230] :
      ( r2_hidden('#skF_10'(A_228,B_229,C_230),B_229)
      | k2_relset_1(A_228,B_229,C_230) = B_229
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_700,plain,
    ( r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),'#skF_13')
    | k2_relset_1('#skF_12','#skF_13','#skF_14') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_74,c_698])).

tff(c_703,plain,(
    r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),'#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_700])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_709,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),B_2)
      | ~ r1_tarski('#skF_13',B_2) ) ),
    inference(resolution,[status(thm)],[c_703,c_2])).

tff(c_1667,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_13'),B_2)
      | ~ r1_tarski('#skF_13',B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1633,c_709])).

tff(c_10,plain,(
    ! [A_9,C_24] :
      ( r2_hidden(k4_tarski('#skF_5'(A_9,k2_relat_1(A_9),C_24),C_24),A_9)
      | ~ r2_hidden(C_24,k2_relat_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1690,plain,(
    ! [E_323,A_324,B_325,C_326] :
      ( ~ r2_hidden(k4_tarski(E_323,'#skF_10'(A_324,B_325,C_326)),C_326)
      | k2_relset_1(A_324,B_325,C_326) = B_325
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(A_324,B_325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3038,plain,(
    ! [A_473,B_474,A_475] :
      ( k2_relset_1(A_473,B_474,A_475) = B_474
      | ~ m1_subset_1(A_475,k1_zfmisc_1(k2_zfmisc_1(A_473,B_474)))
      | ~ r2_hidden('#skF_10'(A_473,B_474,A_475),k2_relat_1(A_475)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1690])).

tff(c_3058,plain,
    ( k2_relset_1('#skF_12','#skF_13','#skF_13') = '#skF_13'
    | ~ m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_12','#skF_13')))
    | ~ r1_tarski('#skF_13',k2_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_1667,c_3038])).

tff(c_3065,plain,
    ( k2_relset_1('#skF_12','#skF_13','#skF_13') = '#skF_13'
    | ~ r1_tarski('#skF_13',k2_relat_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1682,c_3058])).

tff(c_3066,plain,(
    ~ r1_tarski('#skF_13',k2_relat_1('#skF_13')) ),
    inference(negUnitSimplification,[status(thm)],[c_1683,c_3065])).

tff(c_126,plain,(
    ! [A_1,B_2,B_121] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_121)
      | ~ r1_tarski(A_1,B_121)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_121])).

tff(c_30,plain,(
    ! [A_30,B_33] :
      ( k1_funct_1(A_30,B_33) = k1_xboole_0
      | r2_hidden(B_33,k1_relat_1(A_30))
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_246,plain,(
    ! [D_153] :
      ( r2_hidden(D_153,k2_relat_1('#skF_14'))
      | ~ r2_hidden(D_153,'#skF_13')
      | k1_funct_1('#skF_14','#skF_15'(D_153)) = k1_xboole_0
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_30,c_243])).

tff(c_257,plain,(
    ! [D_156] :
      ( r2_hidden(D_156,k2_relat_1('#skF_14'))
      | ~ r2_hidden(D_156,'#skF_13')
      | k1_funct_1('#skF_14','#skF_15'(D_156)) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_78,c_246])).

tff(c_278,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,k2_relat_1('#skF_14'))
      | ~ r2_hidden('#skF_1'(A_1,k2_relat_1('#skF_14')),'#skF_13')
      | k1_funct_1('#skF_14','#skF_15'('#skF_1'(A_1,k2_relat_1('#skF_14')))) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_257,c_4])).

tff(c_3256,plain,(
    ! [A_490] :
      ( r1_tarski(A_490,k2_relat_1('#skF_13'))
      | ~ r2_hidden('#skF_1'(A_490,k2_relat_1('#skF_13')),'#skF_13')
      | k1_funct_1('#skF_13','#skF_15'('#skF_1'(A_490,k2_relat_1('#skF_13')))) = '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1633,c_1633,c_807,c_1633,c_1633,c_278])).

tff(c_1681,plain,(
    ! [D_99] :
      ( k1_funct_1('#skF_13','#skF_15'(D_99)) = D_99
      | ~ r2_hidden(D_99,'#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1633,c_80])).

tff(c_3517,plain,(
    ! [A_521] :
      ( '#skF_1'(A_521,k2_relat_1('#skF_13')) = '#skF_13'
      | ~ r2_hidden('#skF_1'(A_521,k2_relat_1('#skF_13')),'#skF_13')
      | r1_tarski(A_521,k2_relat_1('#skF_13'))
      | ~ r2_hidden('#skF_1'(A_521,k2_relat_1('#skF_13')),'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3256,c_1681])).

tff(c_3523,plain,
    ( '#skF_1'('#skF_13',k2_relat_1('#skF_13')) = '#skF_13'
    | ~ r2_hidden('#skF_1'('#skF_13',k2_relat_1('#skF_13')),'#skF_13')
    | r1_tarski('#skF_13',k2_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_6,c_3517])).

tff(c_3527,plain,
    ( '#skF_1'('#skF_13',k2_relat_1('#skF_13')) = '#skF_13'
    | ~ r2_hidden('#skF_1'('#skF_13',k2_relat_1('#skF_13')),'#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_3066,c_3066,c_3523])).

tff(c_3528,plain,(
    ~ r2_hidden('#skF_1'('#skF_13',k2_relat_1('#skF_13')),'#skF_13') ),
    inference(splitLeft,[status(thm)],[c_3527])).

tff(c_3531,plain,
    ( ~ r1_tarski('#skF_13','#skF_13')
    | r1_tarski('#skF_13',k2_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_126,c_3528])).

tff(c_3537,plain,(
    r1_tarski('#skF_13',k2_relat_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_3531])).

tff(c_3539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3066,c_3537])).

tff(c_3540,plain,(
    '#skF_1'('#skF_13',k2_relat_1('#skF_13')) = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_3527])).

tff(c_50,plain,(
    ! [B_76,A_75] :
      ( ~ r1_tarski(B_76,A_75)
      | ~ r2_hidden(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_110,plain,(
    ! [A_110,B_111] :
      ( ~ r1_tarski(A_110,'#skF_1'(A_110,B_111))
      | r1_tarski(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_101,c_50])).

tff(c_3556,plain,
    ( ~ r1_tarski('#skF_13','#skF_13')
    | r1_tarski('#skF_13',k2_relat_1('#skF_13')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3540,c_110])).

tff(c_3572,plain,(
    r1_tarski('#skF_13',k2_relat_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_3556])).

tff(c_3574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3066,c_3572])).

tff(c_3576,plain,(
    r1_tarski('#skF_12',k1_relat_1('#skF_14')) ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_128,plain,(
    ! [D_123,B_124] :
      ( r2_hidden('#skF_15'(D_123),B_124)
      | ~ r1_tarski('#skF_12',B_124)
      | ~ r2_hidden(D_123,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_82,c_121])).

tff(c_134,plain,(
    ! [D_123,B_2,B_124] :
      ( r2_hidden('#skF_15'(D_123),B_2)
      | ~ r1_tarski(B_124,B_2)
      | ~ r1_tarski('#skF_12',B_124)
      | ~ r2_hidden(D_123,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_128,c_2])).

tff(c_3578,plain,(
    ! [D_123] :
      ( r2_hidden('#skF_15'(D_123),k1_relat_1('#skF_14'))
      | ~ r1_tarski('#skF_12','#skF_12')
      | ~ r2_hidden(D_123,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_3576,c_134])).

tff(c_3581,plain,(
    ! [D_123] :
      ( r2_hidden('#skF_15'(D_123),k1_relat_1('#skF_14'))
      | ~ r2_hidden(D_123,'#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_3578])).

tff(c_3677,plain,(
    ! [B_533,A_534] :
      ( r2_hidden(k4_tarski(B_533,k1_funct_1(A_534,B_533)),A_534)
      | ~ r2_hidden(B_533,k1_relat_1(A_534))
      | ~ v1_funct_1(A_534)
      | ~ v1_relat_1(A_534) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3694,plain,(
    ! [D_99] :
      ( r2_hidden(k4_tarski('#skF_15'(D_99),D_99),'#skF_14')
      | ~ r2_hidden('#skF_15'(D_99),k1_relat_1('#skF_14'))
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14')
      | ~ r2_hidden(D_99,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_3677])).

tff(c_3721,plain,(
    ! [D_538] :
      ( r2_hidden(k4_tarski('#skF_15'(D_538),D_538),'#skF_14')
      | ~ r2_hidden('#skF_15'(D_538),k1_relat_1('#skF_14'))
      | ~ r2_hidden(D_538,'#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_78,c_3694])).

tff(c_3995,plain,(
    ! [D_573,B_574] :
      ( r2_hidden(k4_tarski('#skF_15'(D_573),D_573),B_574)
      | ~ r1_tarski('#skF_14',B_574)
      | ~ r2_hidden('#skF_15'(D_573),k1_relat_1('#skF_14'))
      | ~ r2_hidden(D_573,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_3721,c_2])).

tff(c_12,plain,(
    ! [C_24,A_9,D_27] :
      ( r2_hidden(C_24,k2_relat_1(A_9))
      | ~ r2_hidden(k4_tarski(D_27,C_24),A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4040,plain,(
    ! [D_583,B_584] :
      ( r2_hidden(D_583,k2_relat_1(B_584))
      | ~ r1_tarski('#skF_14',B_584)
      | ~ r2_hidden('#skF_15'(D_583),k1_relat_1('#skF_14'))
      | ~ r2_hidden(D_583,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_3995,c_12])).

tff(c_4062,plain,(
    ! [D_585,B_586] :
      ( r2_hidden(D_585,k2_relat_1(B_586))
      | ~ r1_tarski('#skF_14',B_586)
      | ~ r2_hidden(D_585,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_3581,c_4040])).

tff(c_5057,plain,(
    ! [A_652,B_653] :
      ( r1_tarski(A_652,k2_relat_1(B_653))
      | ~ r1_tarski('#skF_14',B_653)
      | ~ r2_hidden('#skF_1'(A_652,k2_relat_1(B_653)),'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_4062,c_4])).

tff(c_5072,plain,(
    ! [B_654] :
      ( ~ r1_tarski('#skF_14',B_654)
      | r1_tarski('#skF_13',k2_relat_1(B_654)) ) ),
    inference(resolution,[status(thm)],[c_6,c_5057])).

tff(c_4650,plain,(
    ! [A_621,B_622,C_623] :
      ( r2_hidden('#skF_10'(A_621,B_622,C_623),B_622)
      | k2_relset_1(A_621,B_622,C_623) = B_622
      | ~ m1_subset_1(C_623,k1_zfmisc_1(k2_zfmisc_1(A_621,B_622))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4652,plain,
    ( r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),'#skF_13')
    | k2_relset_1('#skF_12','#skF_13','#skF_14') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_74,c_4650])).

tff(c_4655,plain,(
    r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),'#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4652])).

tff(c_4663,plain,(
    ! [B_624] :
      ( r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),B_624)
      | ~ r1_tarski('#skF_13',B_624) ) ),
    inference(resolution,[status(thm)],[c_4655,c_2])).

tff(c_4669,plain,(
    ! [B_2,B_624] :
      ( r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),B_2)
      | ~ r1_tarski(B_624,B_2)
      | ~ r1_tarski('#skF_13',B_624) ) ),
    inference(resolution,[status(thm)],[c_4663,c_2])).

tff(c_5079,plain,(
    ! [B_654] :
      ( r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),k2_relat_1(B_654))
      | ~ r1_tarski('#skF_13','#skF_13')
      | ~ r1_tarski('#skF_14',B_654) ) ),
    inference(resolution,[status(thm)],[c_5072,c_4669])).

tff(c_5094,plain,(
    ! [B_654] :
      ( r2_hidden('#skF_10'('#skF_12','#skF_13','#skF_14'),k2_relat_1(B_654))
      | ~ r1_tarski('#skF_14',B_654) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_5079])).

tff(c_5365,plain,(
    ! [E_671,A_672,B_673,C_674] :
      ( ~ r2_hidden(k4_tarski(E_671,'#skF_10'(A_672,B_673,C_674)),C_674)
      | k2_relset_1(A_672,B_673,C_674) = B_673
      | ~ m1_subset_1(C_674,k1_zfmisc_1(k2_zfmisc_1(A_672,B_673))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_7828,plain,(
    ! [A_807,B_808,A_809] :
      ( k2_relset_1(A_807,B_808,A_809) = B_808
      | ~ m1_subset_1(A_809,k1_zfmisc_1(k2_zfmisc_1(A_807,B_808)))
      | ~ r2_hidden('#skF_10'(A_807,B_808,A_809),k2_relat_1(A_809)) ) ),
    inference(resolution,[status(thm)],[c_10,c_5365])).

tff(c_7843,plain,
    ( k2_relset_1('#skF_12','#skF_13','#skF_14') = '#skF_13'
    | ~ m1_subset_1('#skF_14',k1_zfmisc_1(k2_zfmisc_1('#skF_12','#skF_13')))
    | ~ r1_tarski('#skF_14','#skF_14') ),
    inference(resolution,[status(thm)],[c_5094,c_7828])).

tff(c_7871,plain,(
    k2_relset_1('#skF_12','#skF_13','#skF_14') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_74,c_7843])).

tff(c_7873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_7871])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:10:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.06/2.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.06/2.78  
% 8.06/2.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.06/2.79  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_15 > #skF_14 > #skF_13 > #skF_5 > #skF_11 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_12 > #skF_4 > #skF_10
% 8.06/2.79  
% 8.06/2.79  %Foreground sorts:
% 8.06/2.79  
% 8.06/2.79  
% 8.06/2.79  %Background operators:
% 8.06/2.79  
% 8.06/2.79  
% 8.06/2.79  %Foreground operators:
% 8.06/2.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.06/2.79  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.06/2.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.06/2.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.06/2.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.06/2.79  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.06/2.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.06/2.79  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.06/2.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.06/2.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.06/2.79  tff('#skF_15', type, '#skF_15': $i > $i).
% 8.06/2.79  tff('#skF_14', type, '#skF_14': $i).
% 8.06/2.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.06/2.79  tff('#skF_13', type, '#skF_13': $i).
% 8.06/2.79  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.06/2.79  tff('#skF_11', type, '#skF_11': ($i * $i * $i * $i) > $i).
% 8.06/2.79  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 8.06/2.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.06/2.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.06/2.79  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.06/2.79  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 8.06/2.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.06/2.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.06/2.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.06/2.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.06/2.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.06/2.79  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 8.06/2.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.06/2.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.06/2.79  tff('#skF_12', type, '#skF_12': $i).
% 8.06/2.79  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.06/2.79  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 8.06/2.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.06/2.79  
% 8.06/2.81  tff(f_140, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 8.06/2.81  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.06/2.81  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.06/2.81  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.06/2.81  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.06/2.81  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.06/2.81  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 8.06/2.81  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relset_1)).
% 8.06/2.81  tff(f_47, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 8.06/2.81  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 8.06/2.81  tff(f_87, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.06/2.81  tff(c_72, plain, (k2_relset_1('#skF_12', '#skF_13', '#skF_14')!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.06/2.81  tff(c_101, plain, (![A_110, B_111]: (r2_hidden('#skF_1'(A_110, B_111), A_110) | r1_tarski(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.06/2.81  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.06/2.81  tff(c_109, plain, (![A_110]: (r1_tarski(A_110, A_110))), inference(resolution, [status(thm)], [c_101, c_4])).
% 8.06/2.81  tff(c_74, plain, (m1_subset_1('#skF_14', k1_zfmisc_1(k2_zfmisc_1('#skF_12', '#skF_13')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.06/2.81  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.06/2.81  tff(c_76, plain, (v1_funct_2('#skF_14', '#skF_12', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.06/2.81  tff(c_166, plain, (![A_137, B_138, C_139]: (k1_relset_1(A_137, B_138, C_139)=k1_relat_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.06/2.81  tff(c_170, plain, (k1_relset_1('#skF_12', '#skF_13', '#skF_14')=k1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_74, c_166])).
% 8.06/2.81  tff(c_772, plain, (![B_243, A_244, C_245]: (k1_xboole_0=B_243 | k1_relset_1(A_244, B_243, C_245)=A_244 | ~v1_funct_2(C_245, A_244, B_243) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(A_244, B_243))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.06/2.81  tff(c_775, plain, (k1_xboole_0='#skF_13' | k1_relset_1('#skF_12', '#skF_13', '#skF_14')='#skF_12' | ~v1_funct_2('#skF_14', '#skF_12', '#skF_13')), inference(resolution, [status(thm)], [c_74, c_772])).
% 8.06/2.81  tff(c_778, plain, (k1_xboole_0='#skF_13' | k1_relat_1('#skF_14')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_170, c_775])).
% 8.06/2.81  tff(c_779, plain, (k1_relat_1('#skF_14')='#skF_12'), inference(splitLeft, [status(thm)], [c_778])).
% 8.06/2.81  tff(c_82, plain, (![D_99]: (r2_hidden('#skF_15'(D_99), '#skF_12') | ~r2_hidden(D_99, '#skF_13'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.06/2.81  tff(c_121, plain, (![C_120, B_121, A_122]: (r2_hidden(C_120, B_121) | ~r2_hidden(C_120, A_122) | ~r1_tarski(A_122, B_121))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.06/2.81  tff(c_127, plain, (![D_99, B_121]: (r2_hidden('#skF_15'(D_99), B_121) | ~r1_tarski('#skF_12', B_121) | ~r2_hidden(D_99, '#skF_13'))), inference(resolution, [status(thm)], [c_82, c_121])).
% 8.06/2.81  tff(c_22, plain, (![A_28, B_29]: (v1_relat_1(k2_zfmisc_1(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.06/2.81  tff(c_112, plain, (![B_113, A_114]: (v1_relat_1(B_113) | ~m1_subset_1(B_113, k1_zfmisc_1(A_114)) | ~v1_relat_1(A_114))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.06/2.81  tff(c_115, plain, (v1_relat_1('#skF_14') | ~v1_relat_1(k2_zfmisc_1('#skF_12', '#skF_13'))), inference(resolution, [status(thm)], [c_74, c_112])).
% 8.06/2.81  tff(c_118, plain, (v1_relat_1('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_115])).
% 8.06/2.81  tff(c_78, plain, (v1_funct_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.06/2.81  tff(c_80, plain, (![D_99]: (k1_funct_1('#skF_14', '#skF_15'(D_99))=D_99 | ~r2_hidden(D_99, '#skF_13'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.06/2.81  tff(c_227, plain, (![A_151, D_152]: (r2_hidden(k1_funct_1(A_151, D_152), k2_relat_1(A_151)) | ~r2_hidden(D_152, k1_relat_1(A_151)) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.06/2.81  tff(c_238, plain, (![D_99]: (r2_hidden(D_99, k2_relat_1('#skF_14')) | ~r2_hidden('#skF_15'(D_99), k1_relat_1('#skF_14')) | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14') | ~r2_hidden(D_99, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_227])).
% 8.06/2.81  tff(c_243, plain, (![D_153]: (r2_hidden(D_153, k2_relat_1('#skF_14')) | ~r2_hidden('#skF_15'(D_153), k1_relat_1('#skF_14')) | ~r2_hidden(D_153, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_78, c_238])).
% 8.06/2.81  tff(c_254, plain, (![D_99]: (r2_hidden(D_99, k2_relat_1('#skF_14')) | ~r1_tarski('#skF_12', k1_relat_1('#skF_14')) | ~r2_hidden(D_99, '#skF_13'))), inference(resolution, [status(thm)], [c_127, c_243])).
% 8.06/2.81  tff(c_255, plain, (~r1_tarski('#skF_12', k1_relat_1('#skF_14'))), inference(splitLeft, [status(thm)], [c_254])).
% 8.06/2.81  tff(c_801, plain, (~r1_tarski('#skF_12', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_779, c_255])).
% 8.06/2.81  tff(c_806, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109, c_801])).
% 8.06/2.81  tff(c_808, plain, (k1_relat_1('#skF_14')!='#skF_12'), inference(splitRight, [status(thm)], [c_778])).
% 8.06/2.81  tff(c_807, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_778])).
% 8.06/2.81  tff(c_62, plain, (![C_95, A_93]: (k1_xboole_0=C_95 | ~v1_funct_2(C_95, A_93, k1_xboole_0) | k1_xboole_0=A_93 | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.06/2.81  tff(c_1032, plain, (![C_262, A_263]: (C_262='#skF_13' | ~v1_funct_2(C_262, A_263, '#skF_13') | A_263='#skF_13' | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_263, '#skF_13'))))), inference(demodulation, [status(thm), theory('equality')], [c_807, c_807, c_807, c_807, c_62])).
% 8.06/2.81  tff(c_1035, plain, ('#skF_14'='#skF_13' | ~v1_funct_2('#skF_14', '#skF_12', '#skF_13') | '#skF_13'='#skF_12'), inference(resolution, [status(thm)], [c_74, c_1032])).
% 8.06/2.81  tff(c_1038, plain, ('#skF_14'='#skF_13' | '#skF_13'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1035])).
% 8.06/2.81  tff(c_1039, plain, ('#skF_13'='#skF_12'), inference(splitLeft, [status(thm)], [c_1038])).
% 8.06/2.81  tff(c_1098, plain, (v1_funct_2('#skF_14', '#skF_12', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_1039, c_76])).
% 8.06/2.81  tff(c_1089, plain, (k1_relset_1('#skF_12', '#skF_12', '#skF_14')=k1_relat_1('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_1039, c_170])).
% 8.06/2.81  tff(c_1096, plain, (m1_subset_1('#skF_14', k1_zfmisc_1(k2_zfmisc_1('#skF_12', '#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_1039, c_74])).
% 8.06/2.81  tff(c_68, plain, (![B_94, C_95]: (k1_relset_1(k1_xboole_0, B_94, C_95)=k1_xboole_0 | ~v1_funct_2(C_95, k1_xboole_0, B_94) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_94))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.06/2.81  tff(c_821, plain, (![B_94, C_95]: (k1_relset_1('#skF_13', B_94, C_95)='#skF_13' | ~v1_funct_2(C_95, '#skF_13', B_94) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1('#skF_13', B_94))))), inference(demodulation, [status(thm), theory('equality')], [c_807, c_807, c_807, c_807, c_68])).
% 8.06/2.81  tff(c_1624, plain, (![B_318, C_319]: (k1_relset_1('#skF_12', B_318, C_319)='#skF_12' | ~v1_funct_2(C_319, '#skF_12', B_318) | ~m1_subset_1(C_319, k1_zfmisc_1(k2_zfmisc_1('#skF_12', B_318))))), inference(demodulation, [status(thm), theory('equality')], [c_1039, c_1039, c_1039, c_1039, c_821])).
% 8.06/2.81  tff(c_1627, plain, (k1_relset_1('#skF_12', '#skF_12', '#skF_14')='#skF_12' | ~v1_funct_2('#skF_14', '#skF_12', '#skF_12')), inference(resolution, [status(thm)], [c_1096, c_1624])).
% 8.06/2.81  tff(c_1630, plain, (k1_relat_1('#skF_14')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1098, c_1089, c_1627])).
% 8.06/2.81  tff(c_1632, plain, $false, inference(negUnitSimplification, [status(thm)], [c_808, c_1630])).
% 8.06/2.81  tff(c_1633, plain, ('#skF_14'='#skF_13'), inference(splitRight, [status(thm)], [c_1038])).
% 8.06/2.81  tff(c_1683, plain, (k2_relset_1('#skF_12', '#skF_13', '#skF_13')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_1633, c_72])).
% 8.06/2.81  tff(c_1682, plain, (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_12', '#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_1633, c_74])).
% 8.06/2.81  tff(c_698, plain, (![A_228, B_229, C_230]: (r2_hidden('#skF_10'(A_228, B_229, C_230), B_229) | k2_relset_1(A_228, B_229, C_230)=B_229 | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.06/2.81  tff(c_700, plain, (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), '#skF_13') | k2_relset_1('#skF_12', '#skF_13', '#skF_14')='#skF_13'), inference(resolution, [status(thm)], [c_74, c_698])).
% 8.06/2.81  tff(c_703, plain, (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), '#skF_13')), inference(negUnitSimplification, [status(thm)], [c_72, c_700])).
% 8.06/2.81  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.06/2.81  tff(c_709, plain, (![B_2]: (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), B_2) | ~r1_tarski('#skF_13', B_2))), inference(resolution, [status(thm)], [c_703, c_2])).
% 8.06/2.81  tff(c_1667, plain, (![B_2]: (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_13'), B_2) | ~r1_tarski('#skF_13', B_2))), inference(demodulation, [status(thm), theory('equality')], [c_1633, c_709])).
% 8.06/2.81  tff(c_10, plain, (![A_9, C_24]: (r2_hidden(k4_tarski('#skF_5'(A_9, k2_relat_1(A_9), C_24), C_24), A_9) | ~r2_hidden(C_24, k2_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.06/2.81  tff(c_1690, plain, (![E_323, A_324, B_325, C_326]: (~r2_hidden(k4_tarski(E_323, '#skF_10'(A_324, B_325, C_326)), C_326) | k2_relset_1(A_324, B_325, C_326)=B_325 | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(A_324, B_325))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.06/2.81  tff(c_3038, plain, (![A_473, B_474, A_475]: (k2_relset_1(A_473, B_474, A_475)=B_474 | ~m1_subset_1(A_475, k1_zfmisc_1(k2_zfmisc_1(A_473, B_474))) | ~r2_hidden('#skF_10'(A_473, B_474, A_475), k2_relat_1(A_475)))), inference(resolution, [status(thm)], [c_10, c_1690])).
% 8.06/2.81  tff(c_3058, plain, (k2_relset_1('#skF_12', '#skF_13', '#skF_13')='#skF_13' | ~m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_12', '#skF_13'))) | ~r1_tarski('#skF_13', k2_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_1667, c_3038])).
% 8.06/2.81  tff(c_3065, plain, (k2_relset_1('#skF_12', '#skF_13', '#skF_13')='#skF_13' | ~r1_tarski('#skF_13', k2_relat_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_1682, c_3058])).
% 8.06/2.81  tff(c_3066, plain, (~r1_tarski('#skF_13', k2_relat_1('#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_1683, c_3065])).
% 8.06/2.81  tff(c_126, plain, (![A_1, B_2, B_121]: (r2_hidden('#skF_1'(A_1, B_2), B_121) | ~r1_tarski(A_1, B_121) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_121])).
% 8.06/2.81  tff(c_30, plain, (![A_30, B_33]: (k1_funct_1(A_30, B_33)=k1_xboole_0 | r2_hidden(B_33, k1_relat_1(A_30)) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.06/2.81  tff(c_246, plain, (![D_153]: (r2_hidden(D_153, k2_relat_1('#skF_14')) | ~r2_hidden(D_153, '#skF_13') | k1_funct_1('#skF_14', '#skF_15'(D_153))=k1_xboole_0 | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14'))), inference(resolution, [status(thm)], [c_30, c_243])).
% 8.06/2.81  tff(c_257, plain, (![D_156]: (r2_hidden(D_156, k2_relat_1('#skF_14')) | ~r2_hidden(D_156, '#skF_13') | k1_funct_1('#skF_14', '#skF_15'(D_156))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_118, c_78, c_246])).
% 8.06/2.81  tff(c_278, plain, (![A_1]: (r1_tarski(A_1, k2_relat_1('#skF_14')) | ~r2_hidden('#skF_1'(A_1, k2_relat_1('#skF_14')), '#skF_13') | k1_funct_1('#skF_14', '#skF_15'('#skF_1'(A_1, k2_relat_1('#skF_14'))))=k1_xboole_0)), inference(resolution, [status(thm)], [c_257, c_4])).
% 8.06/2.81  tff(c_3256, plain, (![A_490]: (r1_tarski(A_490, k2_relat_1('#skF_13')) | ~r2_hidden('#skF_1'(A_490, k2_relat_1('#skF_13')), '#skF_13') | k1_funct_1('#skF_13', '#skF_15'('#skF_1'(A_490, k2_relat_1('#skF_13'))))='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_1633, c_1633, c_807, c_1633, c_1633, c_278])).
% 8.06/2.81  tff(c_1681, plain, (![D_99]: (k1_funct_1('#skF_13', '#skF_15'(D_99))=D_99 | ~r2_hidden(D_99, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_1633, c_80])).
% 8.06/2.81  tff(c_3517, plain, (![A_521]: ('#skF_1'(A_521, k2_relat_1('#skF_13'))='#skF_13' | ~r2_hidden('#skF_1'(A_521, k2_relat_1('#skF_13')), '#skF_13') | r1_tarski(A_521, k2_relat_1('#skF_13')) | ~r2_hidden('#skF_1'(A_521, k2_relat_1('#skF_13')), '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_3256, c_1681])).
% 8.06/2.81  tff(c_3523, plain, ('#skF_1'('#skF_13', k2_relat_1('#skF_13'))='#skF_13' | ~r2_hidden('#skF_1'('#skF_13', k2_relat_1('#skF_13')), '#skF_13') | r1_tarski('#skF_13', k2_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_6, c_3517])).
% 8.06/2.81  tff(c_3527, plain, ('#skF_1'('#skF_13', k2_relat_1('#skF_13'))='#skF_13' | ~r2_hidden('#skF_1'('#skF_13', k2_relat_1('#skF_13')), '#skF_13')), inference(negUnitSimplification, [status(thm)], [c_3066, c_3066, c_3523])).
% 8.06/2.81  tff(c_3528, plain, (~r2_hidden('#skF_1'('#skF_13', k2_relat_1('#skF_13')), '#skF_13')), inference(splitLeft, [status(thm)], [c_3527])).
% 8.06/2.81  tff(c_3531, plain, (~r1_tarski('#skF_13', '#skF_13') | r1_tarski('#skF_13', k2_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_126, c_3528])).
% 8.06/2.81  tff(c_3537, plain, (r1_tarski('#skF_13', k2_relat_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_3531])).
% 8.06/2.81  tff(c_3539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3066, c_3537])).
% 8.06/2.81  tff(c_3540, plain, ('#skF_1'('#skF_13', k2_relat_1('#skF_13'))='#skF_13'), inference(splitRight, [status(thm)], [c_3527])).
% 8.06/2.81  tff(c_50, plain, (![B_76, A_75]: (~r1_tarski(B_76, A_75) | ~r2_hidden(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.06/2.81  tff(c_110, plain, (![A_110, B_111]: (~r1_tarski(A_110, '#skF_1'(A_110, B_111)) | r1_tarski(A_110, B_111))), inference(resolution, [status(thm)], [c_101, c_50])).
% 8.06/2.81  tff(c_3556, plain, (~r1_tarski('#skF_13', '#skF_13') | r1_tarski('#skF_13', k2_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_3540, c_110])).
% 8.06/2.81  tff(c_3572, plain, (r1_tarski('#skF_13', k2_relat_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_3556])).
% 8.06/2.81  tff(c_3574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3066, c_3572])).
% 8.06/2.81  tff(c_3576, plain, (r1_tarski('#skF_12', k1_relat_1('#skF_14'))), inference(splitRight, [status(thm)], [c_254])).
% 8.06/2.81  tff(c_128, plain, (![D_123, B_124]: (r2_hidden('#skF_15'(D_123), B_124) | ~r1_tarski('#skF_12', B_124) | ~r2_hidden(D_123, '#skF_13'))), inference(resolution, [status(thm)], [c_82, c_121])).
% 8.06/2.81  tff(c_134, plain, (![D_123, B_2, B_124]: (r2_hidden('#skF_15'(D_123), B_2) | ~r1_tarski(B_124, B_2) | ~r1_tarski('#skF_12', B_124) | ~r2_hidden(D_123, '#skF_13'))), inference(resolution, [status(thm)], [c_128, c_2])).
% 8.06/2.81  tff(c_3578, plain, (![D_123]: (r2_hidden('#skF_15'(D_123), k1_relat_1('#skF_14')) | ~r1_tarski('#skF_12', '#skF_12') | ~r2_hidden(D_123, '#skF_13'))), inference(resolution, [status(thm)], [c_3576, c_134])).
% 8.06/2.81  tff(c_3581, plain, (![D_123]: (r2_hidden('#skF_15'(D_123), k1_relat_1('#skF_14')) | ~r2_hidden(D_123, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_3578])).
% 8.06/2.81  tff(c_3677, plain, (![B_533, A_534]: (r2_hidden(k4_tarski(B_533, k1_funct_1(A_534, B_533)), A_534) | ~r2_hidden(B_533, k1_relat_1(A_534)) | ~v1_funct_1(A_534) | ~v1_relat_1(A_534))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.06/2.81  tff(c_3694, plain, (![D_99]: (r2_hidden(k4_tarski('#skF_15'(D_99), D_99), '#skF_14') | ~r2_hidden('#skF_15'(D_99), k1_relat_1('#skF_14')) | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14') | ~r2_hidden(D_99, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_3677])).
% 8.06/2.81  tff(c_3721, plain, (![D_538]: (r2_hidden(k4_tarski('#skF_15'(D_538), D_538), '#skF_14') | ~r2_hidden('#skF_15'(D_538), k1_relat_1('#skF_14')) | ~r2_hidden(D_538, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_78, c_3694])).
% 8.06/2.81  tff(c_3995, plain, (![D_573, B_574]: (r2_hidden(k4_tarski('#skF_15'(D_573), D_573), B_574) | ~r1_tarski('#skF_14', B_574) | ~r2_hidden('#skF_15'(D_573), k1_relat_1('#skF_14')) | ~r2_hidden(D_573, '#skF_13'))), inference(resolution, [status(thm)], [c_3721, c_2])).
% 8.06/2.81  tff(c_12, plain, (![C_24, A_9, D_27]: (r2_hidden(C_24, k2_relat_1(A_9)) | ~r2_hidden(k4_tarski(D_27, C_24), A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.06/2.81  tff(c_4040, plain, (![D_583, B_584]: (r2_hidden(D_583, k2_relat_1(B_584)) | ~r1_tarski('#skF_14', B_584) | ~r2_hidden('#skF_15'(D_583), k1_relat_1('#skF_14')) | ~r2_hidden(D_583, '#skF_13'))), inference(resolution, [status(thm)], [c_3995, c_12])).
% 8.06/2.81  tff(c_4062, plain, (![D_585, B_586]: (r2_hidden(D_585, k2_relat_1(B_586)) | ~r1_tarski('#skF_14', B_586) | ~r2_hidden(D_585, '#skF_13'))), inference(resolution, [status(thm)], [c_3581, c_4040])).
% 8.06/2.81  tff(c_5057, plain, (![A_652, B_653]: (r1_tarski(A_652, k2_relat_1(B_653)) | ~r1_tarski('#skF_14', B_653) | ~r2_hidden('#skF_1'(A_652, k2_relat_1(B_653)), '#skF_13'))), inference(resolution, [status(thm)], [c_4062, c_4])).
% 8.06/2.81  tff(c_5072, plain, (![B_654]: (~r1_tarski('#skF_14', B_654) | r1_tarski('#skF_13', k2_relat_1(B_654)))), inference(resolution, [status(thm)], [c_6, c_5057])).
% 8.06/2.81  tff(c_4650, plain, (![A_621, B_622, C_623]: (r2_hidden('#skF_10'(A_621, B_622, C_623), B_622) | k2_relset_1(A_621, B_622, C_623)=B_622 | ~m1_subset_1(C_623, k1_zfmisc_1(k2_zfmisc_1(A_621, B_622))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.06/2.81  tff(c_4652, plain, (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), '#skF_13') | k2_relset_1('#skF_12', '#skF_13', '#skF_14')='#skF_13'), inference(resolution, [status(thm)], [c_74, c_4650])).
% 8.06/2.81  tff(c_4655, plain, (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), '#skF_13')), inference(negUnitSimplification, [status(thm)], [c_72, c_4652])).
% 8.06/2.81  tff(c_4663, plain, (![B_624]: (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), B_624) | ~r1_tarski('#skF_13', B_624))), inference(resolution, [status(thm)], [c_4655, c_2])).
% 8.06/2.81  tff(c_4669, plain, (![B_2, B_624]: (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), B_2) | ~r1_tarski(B_624, B_2) | ~r1_tarski('#skF_13', B_624))), inference(resolution, [status(thm)], [c_4663, c_2])).
% 8.06/2.81  tff(c_5079, plain, (![B_654]: (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), k2_relat_1(B_654)) | ~r1_tarski('#skF_13', '#skF_13') | ~r1_tarski('#skF_14', B_654))), inference(resolution, [status(thm)], [c_5072, c_4669])).
% 8.06/2.81  tff(c_5094, plain, (![B_654]: (r2_hidden('#skF_10'('#skF_12', '#skF_13', '#skF_14'), k2_relat_1(B_654)) | ~r1_tarski('#skF_14', B_654))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_5079])).
% 8.06/2.81  tff(c_5365, plain, (![E_671, A_672, B_673, C_674]: (~r2_hidden(k4_tarski(E_671, '#skF_10'(A_672, B_673, C_674)), C_674) | k2_relset_1(A_672, B_673, C_674)=B_673 | ~m1_subset_1(C_674, k1_zfmisc_1(k2_zfmisc_1(A_672, B_673))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.06/2.81  tff(c_7828, plain, (![A_807, B_808, A_809]: (k2_relset_1(A_807, B_808, A_809)=B_808 | ~m1_subset_1(A_809, k1_zfmisc_1(k2_zfmisc_1(A_807, B_808))) | ~r2_hidden('#skF_10'(A_807, B_808, A_809), k2_relat_1(A_809)))), inference(resolution, [status(thm)], [c_10, c_5365])).
% 8.06/2.81  tff(c_7843, plain, (k2_relset_1('#skF_12', '#skF_13', '#skF_14')='#skF_13' | ~m1_subset_1('#skF_14', k1_zfmisc_1(k2_zfmisc_1('#skF_12', '#skF_13'))) | ~r1_tarski('#skF_14', '#skF_14')), inference(resolution, [status(thm)], [c_5094, c_7828])).
% 8.06/2.81  tff(c_7871, plain, (k2_relset_1('#skF_12', '#skF_13', '#skF_14')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_74, c_7843])).
% 8.06/2.81  tff(c_7873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_7871])).
% 8.06/2.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.06/2.81  
% 8.06/2.81  Inference rules
% 8.06/2.81  ----------------------
% 8.06/2.81  #Ref     : 6
% 8.06/2.81  #Sup     : 1730
% 8.06/2.81  #Fact    : 0
% 8.06/2.81  #Define  : 0
% 8.06/2.81  #Split   : 47
% 8.06/2.81  #Chain   : 0
% 8.06/2.81  #Close   : 0
% 8.06/2.81  
% 8.06/2.81  Ordering : KBO
% 8.06/2.81  
% 8.06/2.81  Simplification rules
% 8.06/2.81  ----------------------
% 8.06/2.81  #Subsume      : 552
% 8.06/2.81  #Demod        : 1039
% 8.06/2.81  #Tautology    : 245
% 8.06/2.81  #SimpNegUnit  : 21
% 8.06/2.81  #BackRed      : 154
% 8.06/2.81  
% 8.06/2.81  #Partial instantiations: 0
% 8.06/2.81  #Strategies tried      : 1
% 8.06/2.81  
% 8.06/2.81  Timing (in seconds)
% 8.06/2.81  ----------------------
% 8.06/2.81  Preprocessing        : 0.41
% 8.06/2.81  Parsing              : 0.21
% 8.06/2.81  CNF conversion       : 0.04
% 8.06/2.81  Main loop            : 1.61
% 8.06/2.81  Inferencing          : 0.54
% 8.06/2.81  Reduction            : 0.46
% 8.06/2.81  Demodulation         : 0.29
% 8.06/2.81  BG Simplification    : 0.07
% 8.06/2.81  Subsumption          : 0.42
% 8.06/2.81  Abstraction          : 0.07
% 8.06/2.81  MUC search           : 0.00
% 8.06/2.81  Cooper               : 0.00
% 8.06/2.81  Total                : 2.06
% 8.06/2.81  Index Insertion      : 0.00
% 8.06/2.81  Index Deletion       : 0.00
% 8.06/2.81  Index Matching       : 0.00
% 8.06/2.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
