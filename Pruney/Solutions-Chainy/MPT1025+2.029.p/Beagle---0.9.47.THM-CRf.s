%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:34 EST 2020

% Result     : Theorem 4.85s
% Output     : CNFRefutation 5.01s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 948 expanded)
%              Number of leaves         :   35 ( 341 expanded)
%              Depth                    :   12
%              Number of atoms          :  272 (2977 expanded)
%              Number of equality atoms :   73 ( 963 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_100,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_114,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_100])).

tff(c_286,plain,(
    ! [A_90,B_91,C_92,D_93] :
      ( k7_relset_1(A_90,B_91,C_92,D_93) = k9_relat_1(C_92,D_93)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_299,plain,(
    ! [D_93] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_93) = k9_relat_1('#skF_6',D_93) ),
    inference(resolution,[status(thm)],[c_52,c_286])).

tff(c_50,plain,(
    r2_hidden('#skF_7',k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_302,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_50])).

tff(c_196,plain,(
    ! [A_65,B_66,C_67] :
      ( r2_hidden('#skF_2'(A_65,B_66,C_67),B_66)
      | ~ r2_hidden(A_65,k9_relat_1(C_67,B_66))
      | ~ v1_relat_1(C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_48,plain,(
    ! [F_33] :
      ( k1_funct_1('#skF_6',F_33) != '#skF_7'
      | ~ r2_hidden(F_33,'#skF_5')
      | ~ m1_subset_1(F_33,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_208,plain,(
    ! [A_65,C_67] :
      ( k1_funct_1('#skF_6','#skF_2'(A_65,'#skF_5',C_67)) != '#skF_7'
      | ~ m1_subset_1('#skF_2'(A_65,'#skF_5',C_67),'#skF_3')
      | ~ r2_hidden(A_65,k9_relat_1(C_67,'#skF_5'))
      | ~ v1_relat_1(C_67) ) ),
    inference(resolution,[status(thm)],[c_196,c_48])).

tff(c_329,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_302,c_208])).

tff(c_344,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_329])).

tff(c_357,plain,(
    ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_344])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_141,plain,(
    ! [A_52,B_53,C_54] :
      ( k1_relset_1(A_52,B_53,C_54) = k1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_157,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_141])).

tff(c_1076,plain,(
    ! [B_196,A_197,C_198] :
      ( k1_xboole_0 = B_196
      | k1_relset_1(A_197,B_196,C_198) = A_197
      | ~ v1_funct_2(C_198,A_197,B_196)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_197,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1087,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1076])).

tff(c_1094,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_157,c_1087])).

tff(c_1095,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1094])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_260,plain,(
    ! [A_82,B_83,C_84] :
      ( r2_hidden('#skF_2'(A_82,B_83,C_84),k1_relat_1(C_84))
      | ~ r2_hidden(A_82,k9_relat_1(C_84,B_83))
      | ~ v1_relat_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_269,plain,(
    ! [C_85,A_86,B_87] :
      ( ~ v1_xboole_0(k1_relat_1(C_85))
      | ~ r2_hidden(A_86,k9_relat_1(C_85,B_87))
      | ~ v1_relat_1(C_85) ) ),
    inference(resolution,[status(thm)],[c_260,c_2])).

tff(c_284,plain,(
    ! [C_85,B_87] :
      ( ~ v1_xboole_0(k1_relat_1(C_85))
      | ~ v1_relat_1(C_85)
      | v1_xboole_0(k9_relat_1(C_85,B_87)) ) ),
    inference(resolution,[status(thm)],[c_4,c_269])).

tff(c_76,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_301,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_76])).

tff(c_314,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_284,c_301])).

tff(c_320,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_314])).

tff(c_22,plain,(
    ! [A_7,B_8,C_9] :
      ( r2_hidden('#skF_2'(A_7,B_8,C_9),k1_relat_1(C_9))
      | ~ r2_hidden(A_7,k9_relat_1(C_9,B_8))
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_499,plain,(
    ! [A_115,B_116,C_117] :
      ( r2_hidden(k4_tarski('#skF_2'(A_115,B_116,C_117),A_115),C_117)
      | ~ r2_hidden(A_115,k9_relat_1(C_117,B_116))
      | ~ v1_relat_1(C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [C_15,A_13,B_14] :
      ( k1_funct_1(C_15,A_13) = B_14
      | ~ r2_hidden(k4_tarski(A_13,B_14),C_15)
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_809,plain,(
    ! [C_170,A_171,B_172] :
      ( k1_funct_1(C_170,'#skF_2'(A_171,B_172,C_170)) = A_171
      | ~ v1_funct_1(C_170)
      | ~ r2_hidden(A_171,k9_relat_1(C_170,B_172))
      | ~ v1_relat_1(C_170) ) ),
    inference(resolution,[status(thm)],[c_499,c_26])).

tff(c_817,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_302,c_809])).

tff(c_831,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_56,c_817])).

tff(c_24,plain,(
    ! [A_13,C_15] :
      ( r2_hidden(k4_tarski(A_13,k1_funct_1(C_15,A_13)),C_15)
      | ~ r2_hidden(A_13,k1_relat_1(C_15))
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_838,plain,
    ( r2_hidden(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_831,c_24])).

tff(c_842,plain,
    ( r2_hidden(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_56,c_838])).

tff(c_844,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_842])).

tff(c_974,plain,
    ( ~ r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_844])).

tff(c_981,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_302,c_974])).

tff(c_983,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_842])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_989,plain,
    ( m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_983,c_8])).

tff(c_998,plain,(
    m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_989])).

tff(c_1096,plain,(
    m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1095,c_998])).

tff(c_1101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_357,c_1096])).

tff(c_1102,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1094])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1112,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1102,c_6])).

tff(c_38,plain,(
    ! [C_28,A_26] :
      ( k1_xboole_0 = C_28
      | ~ v1_funct_2(C_28,A_26,k1_xboole_0)
      | k1_xboole_0 = A_26
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1129,plain,(
    ! [C_203,A_204] :
      ( C_203 = '#skF_4'
      | ~ v1_funct_2(C_203,A_204,'#skF_4')
      | A_204 = '#skF_4'
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_204,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1102,c_1102,c_1102,c_1102,c_38])).

tff(c_1140,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_1129])).

tff(c_1147,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1140])).

tff(c_1148,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1147])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_77,plain,(
    ! [F_41] :
      ( k1_funct_1('#skF_6',F_41) != '#skF_7'
      | ~ r2_hidden(F_41,'#skF_5')
      | ~ m1_subset_1(F_41,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_82,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_5')) != '#skF_7'
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_77])).

tff(c_133,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_137,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_133])).

tff(c_138,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_1187,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1148,c_138])).

tff(c_1194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1112,c_1187])).

tff(c_1195,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1147])).

tff(c_419,plain,(
    ! [A_110,C_111] :
      ( r2_hidden(k4_tarski(A_110,k1_funct_1(C_111,A_110)),C_111)
      | ~ r2_hidden(A_110,k1_relat_1(C_111))
      | ~ v1_funct_1(C_111)
      | ~ v1_relat_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_467,plain,(
    ! [C_112,A_113] :
      ( ~ v1_xboole_0(C_112)
      | ~ r2_hidden(A_113,k1_relat_1(C_112))
      | ~ v1_funct_1(C_112)
      | ~ v1_relat_1(C_112) ) ),
    inference(resolution,[status(thm)],[c_419,c_2])).

tff(c_492,plain,(
    ! [C_114] :
      ( ~ v1_xboole_0(C_114)
      | ~ v1_funct_1(C_114)
      | ~ v1_relat_1(C_114)
      | v1_xboole_0(k1_relat_1(C_114)) ) ),
    inference(resolution,[status(thm)],[c_4,c_467])).

tff(c_495,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_492,c_320])).

tff(c_498,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_56,c_495])).

tff(c_1207,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1195,c_498])).

tff(c_1225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1112,c_1207])).

tff(c_1226,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_344])).

tff(c_1421,plain,(
    ! [A_235,B_236,C_237] :
      ( r2_hidden(k4_tarski('#skF_2'(A_235,B_236,C_237),A_235),C_237)
      | ~ r2_hidden(A_235,k9_relat_1(C_237,B_236))
      | ~ v1_relat_1(C_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2003,plain,(
    ! [C_307,A_308,B_309] :
      ( k1_funct_1(C_307,'#skF_2'(A_308,B_309,C_307)) = A_308
      | ~ v1_funct_1(C_307)
      | ~ r2_hidden(A_308,k9_relat_1(C_307,B_309))
      | ~ v1_relat_1(C_307) ) ),
    inference(resolution,[status(thm)],[c_1421,c_26])).

tff(c_2013,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_302,c_2003])).

tff(c_2028,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_56,c_2013])).

tff(c_2030,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1226,c_2028])).

tff(c_2032,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_2050,plain,(
    ! [A_315,B_316,C_317] :
      ( k1_relset_1(A_315,B_316,C_317) = k1_relat_1(C_317)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(A_315,B_316))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2066,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_2050])).

tff(c_2702,plain,(
    ! [B_429,A_430,C_431] :
      ( k1_xboole_0 = B_429
      | k1_relset_1(A_430,B_429,C_431) = A_430
      | ~ v1_funct_2(C_431,A_430,B_429)
      | ~ m1_subset_1(C_431,k1_zfmisc_1(k2_zfmisc_1(A_430,B_429))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2713,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_2702])).

tff(c_2720,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2066,c_2713])).

tff(c_2721,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2720])).

tff(c_2138,plain,(
    ! [A_340,B_341,C_342,D_343] :
      ( k7_relset_1(A_340,B_341,C_342,D_343) = k9_relat_1(C_342,D_343)
      | ~ m1_subset_1(C_342,k1_zfmisc_1(k2_zfmisc_1(A_340,B_341))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2151,plain,(
    ! [D_343] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_343) = k9_relat_1('#skF_6',D_343) ),
    inference(resolution,[status(thm)],[c_52,c_2138])).

tff(c_2154,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2151,c_50])).

tff(c_2190,plain,(
    ! [A_345,B_346,C_347] :
      ( r2_hidden('#skF_2'(A_345,B_346,C_347),k1_relat_1(C_347))
      | ~ r2_hidden(A_345,k9_relat_1(C_347,B_346))
      | ~ v1_relat_1(C_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2199,plain,(
    ! [C_348,A_349,B_350] :
      ( ~ v1_xboole_0(k1_relat_1(C_348))
      | ~ r2_hidden(A_349,k9_relat_1(C_348,B_350))
      | ~ v1_relat_1(C_348) ) ),
    inference(resolution,[status(thm)],[c_2190,c_2])).

tff(c_2202,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2154,c_2199])).

tff(c_2217,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_2202])).

tff(c_2722,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2721,c_2217])).

tff(c_2726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2032,c_2722])).

tff(c_2727,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2720])).

tff(c_2736,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2727,c_6])).

tff(c_2755,plain,(
    ! [C_434,A_435] :
      ( C_434 = '#skF_4'
      | ~ v1_funct_2(C_434,A_435,'#skF_4')
      | A_435 = '#skF_4'
      | ~ m1_subset_1(C_434,k1_zfmisc_1(k2_zfmisc_1(A_435,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2727,c_2727,c_2727,c_2727,c_38])).

tff(c_2766,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_2755])).

tff(c_2773,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2766])).

tff(c_2774,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2773])).

tff(c_2728,plain,(
    k1_relat_1('#skF_6') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2720])).

tff(c_2797,plain,(
    k1_relat_1('#skF_6') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2774,c_2728])).

tff(c_2809,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2774,c_54])).

tff(c_2803,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2774,c_2066])).

tff(c_2808,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2774,c_52])).

tff(c_44,plain,(
    ! [B_27,C_28] :
      ( k1_relset_1(k1_xboole_0,B_27,C_28) = k1_xboole_0
      | ~ v1_funct_2(C_28,k1_xboole_0,B_27)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2865,plain,(
    ! [B_441,C_442] :
      ( k1_relset_1('#skF_4',B_441,C_442) = '#skF_4'
      | ~ v1_funct_2(C_442,'#skF_4',B_441)
      | ~ m1_subset_1(C_442,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_441))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2727,c_2727,c_2727,c_2727,c_44])).

tff(c_2868,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2808,c_2865])).

tff(c_2879,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2809,c_2803,c_2868])).

tff(c_2881,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2797,c_2879])).

tff(c_2882,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2773])).

tff(c_2344,plain,(
    ! [A_368,B_369,C_370] :
      ( r2_hidden(k4_tarski('#skF_2'(A_368,B_369,C_370),A_368),C_370)
      | ~ r2_hidden(A_368,k9_relat_1(C_370,B_369))
      | ~ v1_relat_1(C_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2391,plain,(
    ! [C_371,A_372,B_373] :
      ( ~ v1_xboole_0(C_371)
      | ~ r2_hidden(A_372,k9_relat_1(C_371,B_373))
      | ~ v1_relat_1(C_371) ) ),
    inference(resolution,[status(thm)],[c_2344,c_2])).

tff(c_2402,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2154,c_2391])).

tff(c_2419,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_2402])).

tff(c_2888,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2882,c_2419])).

tff(c_2906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2736,c_2888])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:51:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.85/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/1.99  
% 5.01/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/1.99  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 5.01/1.99  
% 5.01/1.99  %Foreground sorts:
% 5.01/1.99  
% 5.01/1.99  
% 5.01/1.99  %Background operators:
% 5.01/1.99  
% 5.01/1.99  
% 5.01/1.99  %Foreground operators:
% 5.01/1.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.01/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.01/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.01/1.99  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.01/1.99  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.01/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.01/1.99  tff('#skF_7', type, '#skF_7': $i).
% 5.01/1.99  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.01/1.99  tff('#skF_5', type, '#skF_5': $i).
% 5.01/1.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.01/1.99  tff('#skF_6', type, '#skF_6': $i).
% 5.01/1.99  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.01/1.99  tff('#skF_3', type, '#skF_3': $i).
% 5.01/1.99  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.01/1.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.01/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.01/1.99  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.01/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.01/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.01/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.01/1.99  tff('#skF_4', type, '#skF_4': $i).
% 5.01/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.01/1.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.01/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.01/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.01/1.99  
% 5.01/2.01  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 5.01/2.01  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.01/2.01  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.01/2.01  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 5.01/2.01  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.01/2.01  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.01/2.01  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.01/2.01  tff(f_66, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 5.01/2.01  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.01/2.01  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.01/2.01  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.01/2.01  tff(c_100, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.01/2.01  tff(c_114, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_100])).
% 5.01/2.01  tff(c_286, plain, (![A_90, B_91, C_92, D_93]: (k7_relset_1(A_90, B_91, C_92, D_93)=k9_relat_1(C_92, D_93) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.01/2.01  tff(c_299, plain, (![D_93]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_93)=k9_relat_1('#skF_6', D_93))), inference(resolution, [status(thm)], [c_52, c_286])).
% 5.01/2.01  tff(c_50, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.01/2.01  tff(c_302, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_50])).
% 5.01/2.01  tff(c_196, plain, (![A_65, B_66, C_67]: (r2_hidden('#skF_2'(A_65, B_66, C_67), B_66) | ~r2_hidden(A_65, k9_relat_1(C_67, B_66)) | ~v1_relat_1(C_67))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.01/2.01  tff(c_48, plain, (![F_33]: (k1_funct_1('#skF_6', F_33)!='#skF_7' | ~r2_hidden(F_33, '#skF_5') | ~m1_subset_1(F_33, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.01/2.01  tff(c_208, plain, (![A_65, C_67]: (k1_funct_1('#skF_6', '#skF_2'(A_65, '#skF_5', C_67))!='#skF_7' | ~m1_subset_1('#skF_2'(A_65, '#skF_5', C_67), '#skF_3') | ~r2_hidden(A_65, k9_relat_1(C_67, '#skF_5')) | ~v1_relat_1(C_67))), inference(resolution, [status(thm)], [c_196, c_48])).
% 5.01/2.01  tff(c_329, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_302, c_208])).
% 5.01/2.01  tff(c_344, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_329])).
% 5.01/2.01  tff(c_357, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(splitLeft, [status(thm)], [c_344])).
% 5.01/2.01  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.01/2.01  tff(c_141, plain, (![A_52, B_53, C_54]: (k1_relset_1(A_52, B_53, C_54)=k1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.01/2.01  tff(c_157, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_141])).
% 5.01/2.01  tff(c_1076, plain, (![B_196, A_197, C_198]: (k1_xboole_0=B_196 | k1_relset_1(A_197, B_196, C_198)=A_197 | ~v1_funct_2(C_198, A_197, B_196) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_197, B_196))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.01/2.01  tff(c_1087, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_1076])).
% 5.01/2.01  tff(c_1094, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_157, c_1087])).
% 5.01/2.01  tff(c_1095, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_1094])).
% 5.01/2.01  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.01/2.01  tff(c_260, plain, (![A_82, B_83, C_84]: (r2_hidden('#skF_2'(A_82, B_83, C_84), k1_relat_1(C_84)) | ~r2_hidden(A_82, k9_relat_1(C_84, B_83)) | ~v1_relat_1(C_84))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.01/2.01  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.01/2.01  tff(c_269, plain, (![C_85, A_86, B_87]: (~v1_xboole_0(k1_relat_1(C_85)) | ~r2_hidden(A_86, k9_relat_1(C_85, B_87)) | ~v1_relat_1(C_85))), inference(resolution, [status(thm)], [c_260, c_2])).
% 5.01/2.01  tff(c_284, plain, (![C_85, B_87]: (~v1_xboole_0(k1_relat_1(C_85)) | ~v1_relat_1(C_85) | v1_xboole_0(k9_relat_1(C_85, B_87)))), inference(resolution, [status(thm)], [c_4, c_269])).
% 5.01/2.01  tff(c_76, plain, (~v1_xboole_0(k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_2])).
% 5.01/2.01  tff(c_301, plain, (~v1_xboole_0(k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_76])).
% 5.01/2.01  tff(c_314, plain, (~v1_xboole_0(k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_284, c_301])).
% 5.01/2.01  tff(c_320, plain, (~v1_xboole_0(k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_314])).
% 5.01/2.01  tff(c_22, plain, (![A_7, B_8, C_9]: (r2_hidden('#skF_2'(A_7, B_8, C_9), k1_relat_1(C_9)) | ~r2_hidden(A_7, k9_relat_1(C_9, B_8)) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.01/2.01  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.01/2.01  tff(c_499, plain, (![A_115, B_116, C_117]: (r2_hidden(k4_tarski('#skF_2'(A_115, B_116, C_117), A_115), C_117) | ~r2_hidden(A_115, k9_relat_1(C_117, B_116)) | ~v1_relat_1(C_117))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.01/2.01  tff(c_26, plain, (![C_15, A_13, B_14]: (k1_funct_1(C_15, A_13)=B_14 | ~r2_hidden(k4_tarski(A_13, B_14), C_15) | ~v1_funct_1(C_15) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.01/2.01  tff(c_809, plain, (![C_170, A_171, B_172]: (k1_funct_1(C_170, '#skF_2'(A_171, B_172, C_170))=A_171 | ~v1_funct_1(C_170) | ~r2_hidden(A_171, k9_relat_1(C_170, B_172)) | ~v1_relat_1(C_170))), inference(resolution, [status(thm)], [c_499, c_26])).
% 5.01/2.01  tff(c_817, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_302, c_809])).
% 5.01/2.01  tff(c_831, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_56, c_817])).
% 5.01/2.01  tff(c_24, plain, (![A_13, C_15]: (r2_hidden(k4_tarski(A_13, k1_funct_1(C_15, A_13)), C_15) | ~r2_hidden(A_13, k1_relat_1(C_15)) | ~v1_funct_1(C_15) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.01/2.01  tff(c_838, plain, (r2_hidden(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_831, c_24])).
% 5.01/2.01  tff(c_842, plain, (r2_hidden(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_56, c_838])).
% 5.01/2.01  tff(c_844, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_842])).
% 5.01/2.01  tff(c_974, plain, (~r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_22, c_844])).
% 5.01/2.01  tff(c_981, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_302, c_974])).
% 5.01/2.01  tff(c_983, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_842])).
% 5.01/2.01  tff(c_8, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.01/2.01  tff(c_989, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | v1_xboole_0(k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_983, c_8])).
% 5.01/2.01  tff(c_998, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_320, c_989])).
% 5.01/2.01  tff(c_1096, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1095, c_998])).
% 5.01/2.01  tff(c_1101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_357, c_1096])).
% 5.01/2.01  tff(c_1102, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1094])).
% 5.01/2.01  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.01/2.01  tff(c_1112, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1102, c_6])).
% 5.01/2.01  tff(c_38, plain, (![C_28, A_26]: (k1_xboole_0=C_28 | ~v1_funct_2(C_28, A_26, k1_xboole_0) | k1_xboole_0=A_26 | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.01/2.01  tff(c_1129, plain, (![C_203, A_204]: (C_203='#skF_4' | ~v1_funct_2(C_203, A_204, '#skF_4') | A_204='#skF_4' | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_204, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_1102, c_1102, c_1102, c_1102, c_38])).
% 5.01/2.01  tff(c_1140, plain, ('#skF_6'='#skF_4' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_52, c_1129])).
% 5.01/2.01  tff(c_1147, plain, ('#skF_6'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1140])).
% 5.01/2.01  tff(c_1148, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_1147])).
% 5.01/2.01  tff(c_12, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~v1_xboole_0(B_6) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.01/2.01  tff(c_77, plain, (![F_41]: (k1_funct_1('#skF_6', F_41)!='#skF_7' | ~r2_hidden(F_41, '#skF_5') | ~m1_subset_1(F_41, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.01/2.01  tff(c_82, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5'))!='#skF_7' | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_3') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_77])).
% 5.01/2.01  tff(c_133, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_82])).
% 5.01/2.01  tff(c_137, plain, (~v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_133])).
% 5.01/2.01  tff(c_138, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_137])).
% 5.01/2.01  tff(c_1187, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1148, c_138])).
% 5.01/2.01  tff(c_1194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1112, c_1187])).
% 5.01/2.01  tff(c_1195, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_1147])).
% 5.01/2.01  tff(c_419, plain, (![A_110, C_111]: (r2_hidden(k4_tarski(A_110, k1_funct_1(C_111, A_110)), C_111) | ~r2_hidden(A_110, k1_relat_1(C_111)) | ~v1_funct_1(C_111) | ~v1_relat_1(C_111))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.01/2.01  tff(c_467, plain, (![C_112, A_113]: (~v1_xboole_0(C_112) | ~r2_hidden(A_113, k1_relat_1(C_112)) | ~v1_funct_1(C_112) | ~v1_relat_1(C_112))), inference(resolution, [status(thm)], [c_419, c_2])).
% 5.01/2.01  tff(c_492, plain, (![C_114]: (~v1_xboole_0(C_114) | ~v1_funct_1(C_114) | ~v1_relat_1(C_114) | v1_xboole_0(k1_relat_1(C_114)))), inference(resolution, [status(thm)], [c_4, c_467])).
% 5.01/2.01  tff(c_495, plain, (~v1_xboole_0('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_492, c_320])).
% 5.01/2.01  tff(c_498, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_56, c_495])).
% 5.01/2.01  tff(c_1207, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1195, c_498])).
% 5.01/2.01  tff(c_1225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1112, c_1207])).
% 5.01/2.01  tff(c_1226, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7'), inference(splitRight, [status(thm)], [c_344])).
% 5.01/2.01  tff(c_1421, plain, (![A_235, B_236, C_237]: (r2_hidden(k4_tarski('#skF_2'(A_235, B_236, C_237), A_235), C_237) | ~r2_hidden(A_235, k9_relat_1(C_237, B_236)) | ~v1_relat_1(C_237))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.01/2.01  tff(c_2003, plain, (![C_307, A_308, B_309]: (k1_funct_1(C_307, '#skF_2'(A_308, B_309, C_307))=A_308 | ~v1_funct_1(C_307) | ~r2_hidden(A_308, k9_relat_1(C_307, B_309)) | ~v1_relat_1(C_307))), inference(resolution, [status(thm)], [c_1421, c_26])).
% 5.01/2.01  tff(c_2013, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_302, c_2003])).
% 5.01/2.01  tff(c_2028, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_56, c_2013])).
% 5.01/2.01  tff(c_2030, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1226, c_2028])).
% 5.01/2.01  tff(c_2032, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_137])).
% 5.01/2.01  tff(c_2050, plain, (![A_315, B_316, C_317]: (k1_relset_1(A_315, B_316, C_317)=k1_relat_1(C_317) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(A_315, B_316))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.01/2.01  tff(c_2066, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_2050])).
% 5.01/2.01  tff(c_2702, plain, (![B_429, A_430, C_431]: (k1_xboole_0=B_429 | k1_relset_1(A_430, B_429, C_431)=A_430 | ~v1_funct_2(C_431, A_430, B_429) | ~m1_subset_1(C_431, k1_zfmisc_1(k2_zfmisc_1(A_430, B_429))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.01/2.01  tff(c_2713, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_2702])).
% 5.01/2.01  tff(c_2720, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2066, c_2713])).
% 5.01/2.01  tff(c_2721, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_2720])).
% 5.01/2.01  tff(c_2138, plain, (![A_340, B_341, C_342, D_343]: (k7_relset_1(A_340, B_341, C_342, D_343)=k9_relat_1(C_342, D_343) | ~m1_subset_1(C_342, k1_zfmisc_1(k2_zfmisc_1(A_340, B_341))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.01/2.01  tff(c_2151, plain, (![D_343]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_343)=k9_relat_1('#skF_6', D_343))), inference(resolution, [status(thm)], [c_52, c_2138])).
% 5.01/2.01  tff(c_2154, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2151, c_50])).
% 5.01/2.01  tff(c_2190, plain, (![A_345, B_346, C_347]: (r2_hidden('#skF_2'(A_345, B_346, C_347), k1_relat_1(C_347)) | ~r2_hidden(A_345, k9_relat_1(C_347, B_346)) | ~v1_relat_1(C_347))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.01/2.01  tff(c_2199, plain, (![C_348, A_349, B_350]: (~v1_xboole_0(k1_relat_1(C_348)) | ~r2_hidden(A_349, k9_relat_1(C_348, B_350)) | ~v1_relat_1(C_348))), inference(resolution, [status(thm)], [c_2190, c_2])).
% 5.01/2.01  tff(c_2202, plain, (~v1_xboole_0(k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2154, c_2199])).
% 5.01/2.01  tff(c_2217, plain, (~v1_xboole_0(k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_2202])).
% 5.01/2.01  tff(c_2722, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2721, c_2217])).
% 5.01/2.01  tff(c_2726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2032, c_2722])).
% 5.01/2.01  tff(c_2727, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2720])).
% 5.01/2.01  tff(c_2736, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2727, c_6])).
% 5.01/2.01  tff(c_2755, plain, (![C_434, A_435]: (C_434='#skF_4' | ~v1_funct_2(C_434, A_435, '#skF_4') | A_435='#skF_4' | ~m1_subset_1(C_434, k1_zfmisc_1(k2_zfmisc_1(A_435, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_2727, c_2727, c_2727, c_2727, c_38])).
% 5.01/2.01  tff(c_2766, plain, ('#skF_6'='#skF_4' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_52, c_2755])).
% 5.01/2.01  tff(c_2773, plain, ('#skF_6'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2766])).
% 5.01/2.01  tff(c_2774, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_2773])).
% 5.01/2.01  tff(c_2728, plain, (k1_relat_1('#skF_6')!='#skF_3'), inference(splitRight, [status(thm)], [c_2720])).
% 5.01/2.01  tff(c_2797, plain, (k1_relat_1('#skF_6')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2774, c_2728])).
% 5.01/2.01  tff(c_2809, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2774, c_54])).
% 5.01/2.01  tff(c_2803, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2774, c_2066])).
% 5.01/2.01  tff(c_2808, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2774, c_52])).
% 5.01/2.01  tff(c_44, plain, (![B_27, C_28]: (k1_relset_1(k1_xboole_0, B_27, C_28)=k1_xboole_0 | ~v1_funct_2(C_28, k1_xboole_0, B_27) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_27))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.01/2.01  tff(c_2865, plain, (![B_441, C_442]: (k1_relset_1('#skF_4', B_441, C_442)='#skF_4' | ~v1_funct_2(C_442, '#skF_4', B_441) | ~m1_subset_1(C_442, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_441))))), inference(demodulation, [status(thm), theory('equality')], [c_2727, c_2727, c_2727, c_2727, c_44])).
% 5.01/2.01  tff(c_2868, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_2808, c_2865])).
% 5.01/2.01  tff(c_2879, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2809, c_2803, c_2868])).
% 5.01/2.01  tff(c_2881, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2797, c_2879])).
% 5.01/2.01  tff(c_2882, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_2773])).
% 5.01/2.01  tff(c_2344, plain, (![A_368, B_369, C_370]: (r2_hidden(k4_tarski('#skF_2'(A_368, B_369, C_370), A_368), C_370) | ~r2_hidden(A_368, k9_relat_1(C_370, B_369)) | ~v1_relat_1(C_370))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.01/2.01  tff(c_2391, plain, (![C_371, A_372, B_373]: (~v1_xboole_0(C_371) | ~r2_hidden(A_372, k9_relat_1(C_371, B_373)) | ~v1_relat_1(C_371))), inference(resolution, [status(thm)], [c_2344, c_2])).
% 5.01/2.01  tff(c_2402, plain, (~v1_xboole_0('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2154, c_2391])).
% 5.01/2.01  tff(c_2419, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_2402])).
% 5.01/2.01  tff(c_2888, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2882, c_2419])).
% 5.01/2.01  tff(c_2906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2736, c_2888])).
% 5.01/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/2.01  
% 5.01/2.01  Inference rules
% 5.01/2.01  ----------------------
% 5.01/2.01  #Ref     : 0
% 5.01/2.01  #Sup     : 532
% 5.01/2.01  #Fact    : 0
% 5.01/2.01  #Define  : 0
% 5.01/2.01  #Split   : 21
% 5.01/2.01  #Chain   : 0
% 5.01/2.01  #Close   : 0
% 5.01/2.01  
% 5.01/2.01  Ordering : KBO
% 5.01/2.01  
% 5.01/2.01  Simplification rules
% 5.01/2.01  ----------------------
% 5.01/2.01  #Subsume      : 127
% 5.01/2.01  #Demod        : 320
% 5.01/2.01  #Tautology    : 67
% 5.01/2.01  #SimpNegUnit  : 51
% 5.01/2.01  #BackRed      : 115
% 5.01/2.01  
% 5.01/2.01  #Partial instantiations: 0
% 5.01/2.01  #Strategies tried      : 1
% 5.01/2.01  
% 5.01/2.01  Timing (in seconds)
% 5.01/2.01  ----------------------
% 5.01/2.01  Preprocessing        : 0.33
% 5.01/2.01  Parsing              : 0.15
% 5.01/2.01  CNF conversion       : 0.02
% 5.01/2.01  Main loop            : 0.85
% 5.01/2.01  Inferencing          : 0.30
% 5.01/2.01  Reduction            : 0.23
% 5.01/2.01  Demodulation         : 0.15
% 5.01/2.01  BG Simplification    : 0.03
% 5.01/2.01  Subsumption          : 0.21
% 5.01/2.01  Abstraction          : 0.04
% 5.01/2.01  MUC search           : 0.00
% 5.01/2.01  Cooper               : 0.00
% 5.01/2.01  Total                : 1.22
% 5.01/2.01  Index Insertion      : 0.00
% 5.01/2.01  Index Deletion       : 0.00
% 5.01/2.02  Index Matching       : 0.00
% 5.01/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
