%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:37 EST 2020

% Result     : Theorem 4.32s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 277 expanded)
%              Number of leaves         :   33 ( 110 expanded)
%              Depth                    :   15
%              Number of atoms          :  165 ( 714 expanded)
%              Number of equality atoms :   17 (  87 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_99,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_22,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_66,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_72,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_66])).

tff(c_76,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_72])).

tff(c_222,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( k7_relset_1(A_96,B_97,C_98,D_99) = k9_relat_1(C_98,D_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_237,plain,(
    ! [D_99] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_99) = k9_relat_1('#skF_6',D_99) ),
    inference(resolution,[status(thm)],[c_44,c_222])).

tff(c_42,plain,(
    r2_hidden('#skF_7',k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_240,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_42])).

tff(c_180,plain,(
    ! [A_86,B_87,C_88] :
      ( r2_hidden('#skF_2'(A_86,B_87,C_88),B_87)
      | ~ r2_hidden(A_86,k9_relat_1(C_88,B_87))
      | ~ v1_relat_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_40,plain,(
    ! [F_36] :
      ( k1_funct_1('#skF_6',F_36) != '#skF_7'
      | ~ r2_hidden(F_36,'#skF_5')
      | ~ m1_subset_1(F_36,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_321,plain,(
    ! [A_118,C_119] :
      ( k1_funct_1('#skF_6','#skF_2'(A_118,'#skF_5',C_119)) != '#skF_7'
      | ~ m1_subset_1('#skF_2'(A_118,'#skF_5',C_119),'#skF_3')
      | ~ r2_hidden(A_118,k9_relat_1(C_119,'#skF_5'))
      | ~ v1_relat_1(C_119) ) ),
    inference(resolution,[status(thm)],[c_180,c_40])).

tff(c_324,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_240,c_321])).

tff(c_339,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_324])).

tff(c_352,plain,(
    ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_339])).

tff(c_85,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_1'(A_52,B_53),A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_97,plain,(
    ! [A_52] : r1_tarski(A_52,A_52) ),
    inference(resolution,[status(thm)],[c_85,c_4])).

tff(c_56,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_116,plain,(
    ! [C_57,B_58,A_59] :
      ( r2_hidden(C_57,B_58)
      | ~ r2_hidden(C_57,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_137,plain,(
    ! [A_71,B_72,B_73] :
      ( r2_hidden('#skF_1'(A_71,B_72),B_73)
      | ~ r1_tarski(A_71,B_73)
      | r1_tarski(A_71,B_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_116])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_432,plain,(
    ! [A_136,B_137,B_138,B_139] :
      ( r2_hidden('#skF_1'(A_136,B_137),B_138)
      | ~ r1_tarski(B_139,B_138)
      | ~ r1_tarski(A_136,B_139)
      | r1_tarski(A_136,B_137) ) ),
    inference(resolution,[status(thm)],[c_137,c_2])).

tff(c_446,plain,(
    ! [A_140,B_141] :
      ( r2_hidden('#skF_1'(A_140,B_141),k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r1_tarski(A_140,'#skF_6')
      | r1_tarski(A_140,B_141) ) ),
    inference(resolution,[status(thm)],[c_64,c_432])).

tff(c_457,plain,(
    ! [A_140] :
      ( ~ r1_tarski(A_140,'#skF_6')
      | r1_tarski(A_140,k2_zfmisc_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_446,c_4])).

tff(c_30,plain,(
    ! [A_19,B_20,C_21] :
      ( r2_hidden('#skF_2'(A_19,B_20,C_21),k1_relat_1(C_21))
      | ~ r2_hidden(A_19,k9_relat_1(C_21,B_20))
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_366,plain,(
    ! [A_126,B_127,C_128] :
      ( r2_hidden(k4_tarski('#skF_2'(A_126,B_127,C_128),A_126),C_128)
      | ~ r2_hidden(A_126,k9_relat_1(C_128,B_127))
      | ~ v1_relat_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_34,plain,(
    ! [C_27,A_25,B_26] :
      ( k1_funct_1(C_27,A_25) = B_26
      | ~ r2_hidden(k4_tarski(A_25,B_26),C_27)
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_857,plain,(
    ! [C_196,A_197,B_198] :
      ( k1_funct_1(C_196,'#skF_2'(A_197,B_198,C_196)) = A_197
      | ~ v1_funct_1(C_196)
      | ~ r2_hidden(A_197,k9_relat_1(C_196,B_198))
      | ~ v1_relat_1(C_196) ) ),
    inference(resolution,[status(thm)],[c_366,c_34])).

tff(c_871,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_240,c_857])).

tff(c_887,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_48,c_871])).

tff(c_495,plain,(
    ! [A_145,C_146] :
      ( r2_hidden(k4_tarski(A_145,k1_funct_1(C_146,A_145)),C_146)
      | ~ r2_hidden(A_145,k1_relat_1(C_146))
      | ~ v1_funct_1(C_146)
      | ~ v1_relat_1(C_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_544,plain,(
    ! [A_145,C_146] :
      ( m1_subset_1(k4_tarski(A_145,k1_funct_1(C_146,A_145)),C_146)
      | ~ r2_hidden(A_145,k1_relat_1(C_146))
      | ~ v1_funct_1(C_146)
      | ~ v1_relat_1(C_146) ) ),
    inference(resolution,[status(thm)],[c_495,c_14])).

tff(c_894,plain,
    ( m1_subset_1(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_887,c_544])).

tff(c_901,plain,
    ( m1_subset_1(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_48,c_894])).

tff(c_906,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_901])).

tff(c_912,plain,
    ( ~ r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_906])).

tff(c_919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_240,c_912])).

tff(c_921,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_901])).

tff(c_32,plain,(
    ! [A_25,C_27] :
      ( r2_hidden(k4_tarski(A_25,k1_funct_1(C_27,A_25)),C_27)
      | ~ r2_hidden(A_25,k1_relat_1(C_27))
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_897,plain,
    ( r2_hidden(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_887,c_32])).

tff(c_903,plain,
    ( r2_hidden(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_48,c_897])).

tff(c_1174,plain,(
    r2_hidden(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_903])).

tff(c_1201,plain,(
    ! [B_220] :
      ( r2_hidden(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),B_220)
      | ~ r1_tarski('#skF_6',B_220) ) ),
    inference(resolution,[status(thm)],[c_1174,c_2])).

tff(c_12,plain,(
    ! [A_6,C_8,B_7,D_9] :
      ( r2_hidden(A_6,C_8)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1558,plain,(
    ! [C_237,D_238] :
      ( r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),C_237)
      | ~ r1_tarski('#skF_6',k2_zfmisc_1(C_237,D_238)) ) ),
    inference(resolution,[status(thm)],[c_1201,c_12])).

tff(c_1561,plain,
    ( r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3')
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_457,c_1558])).

tff(c_1566,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_1561])).

tff(c_1576,plain,(
    m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1566,c_14])).

tff(c_1583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_352,c_1576])).

tff(c_1584,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_1601,plain,(
    ! [A_247,B_248,C_249] :
      ( r2_hidden(k4_tarski('#skF_2'(A_247,B_248,C_249),A_247),C_249)
      | ~ r2_hidden(A_247,k9_relat_1(C_249,B_248))
      | ~ v1_relat_1(C_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2005,plain,(
    ! [C_306,A_307,B_308] :
      ( k1_funct_1(C_306,'#skF_2'(A_307,B_308,C_306)) = A_307
      | ~ v1_funct_1(C_306)
      | ~ r2_hidden(A_307,k9_relat_1(C_306,B_308))
      | ~ v1_relat_1(C_306) ) ),
    inference(resolution,[status(thm)],[c_1601,c_34])).

tff(c_2016,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_240,c_2005])).

tff(c_2031,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_48,c_2016])).

tff(c_2033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1584,c_2031])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:46:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.32/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/1.79  
% 4.37/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/1.79  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 4.37/1.79  
% 4.37/1.79  %Foreground sorts:
% 4.37/1.79  
% 4.37/1.79  
% 4.37/1.79  %Background operators:
% 4.37/1.79  
% 4.37/1.79  
% 4.37/1.79  %Foreground operators:
% 4.37/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.37/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.37/1.79  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.37/1.79  tff('#skF_7', type, '#skF_7': $i).
% 4.37/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.37/1.79  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.37/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.37/1.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.37/1.79  tff('#skF_6', type, '#skF_6': $i).
% 4.37/1.79  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.37/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.37/1.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.37/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.37/1.79  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.37/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.37/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.37/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.37/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.37/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.37/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.37/1.79  
% 4.50/1.81  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.50/1.81  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 4.50/1.81  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.50/1.81  tff(f_80, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.50/1.81  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 4.50/1.81  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.50/1.81  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.50/1.81  tff(f_76, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 4.50/1.81  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.50/1.81  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.50/1.81  tff(c_22, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.50/1.81  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.50/1.81  tff(c_66, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.50/1.81  tff(c_72, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_66])).
% 4.50/1.81  tff(c_76, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_72])).
% 4.50/1.81  tff(c_222, plain, (![A_96, B_97, C_98, D_99]: (k7_relset_1(A_96, B_97, C_98, D_99)=k9_relat_1(C_98, D_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.50/1.81  tff(c_237, plain, (![D_99]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_99)=k9_relat_1('#skF_6', D_99))), inference(resolution, [status(thm)], [c_44, c_222])).
% 4.50/1.81  tff(c_42, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.50/1.81  tff(c_240, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_237, c_42])).
% 4.50/1.81  tff(c_180, plain, (![A_86, B_87, C_88]: (r2_hidden('#skF_2'(A_86, B_87, C_88), B_87) | ~r2_hidden(A_86, k9_relat_1(C_88, B_87)) | ~v1_relat_1(C_88))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.50/1.81  tff(c_40, plain, (![F_36]: (k1_funct_1('#skF_6', F_36)!='#skF_7' | ~r2_hidden(F_36, '#skF_5') | ~m1_subset_1(F_36, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.50/1.81  tff(c_321, plain, (![A_118, C_119]: (k1_funct_1('#skF_6', '#skF_2'(A_118, '#skF_5', C_119))!='#skF_7' | ~m1_subset_1('#skF_2'(A_118, '#skF_5', C_119), '#skF_3') | ~r2_hidden(A_118, k9_relat_1(C_119, '#skF_5')) | ~v1_relat_1(C_119))), inference(resolution, [status(thm)], [c_180, c_40])).
% 4.50/1.81  tff(c_324, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_240, c_321])).
% 4.50/1.81  tff(c_339, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_324])).
% 4.50/1.81  tff(c_352, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(splitLeft, [status(thm)], [c_339])).
% 4.50/1.81  tff(c_85, plain, (![A_52, B_53]: (r2_hidden('#skF_1'(A_52, B_53), A_52) | r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.50/1.81  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.50/1.81  tff(c_97, plain, (![A_52]: (r1_tarski(A_52, A_52))), inference(resolution, [status(thm)], [c_85, c_4])).
% 4.50/1.81  tff(c_56, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | ~m1_subset_1(A_43, k1_zfmisc_1(B_44)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.50/1.81  tff(c_64, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_56])).
% 4.50/1.81  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.50/1.81  tff(c_116, plain, (![C_57, B_58, A_59]: (r2_hidden(C_57, B_58) | ~r2_hidden(C_57, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.50/1.81  tff(c_137, plain, (![A_71, B_72, B_73]: (r2_hidden('#skF_1'(A_71, B_72), B_73) | ~r1_tarski(A_71, B_73) | r1_tarski(A_71, B_72))), inference(resolution, [status(thm)], [c_6, c_116])).
% 4.50/1.81  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.50/1.81  tff(c_432, plain, (![A_136, B_137, B_138, B_139]: (r2_hidden('#skF_1'(A_136, B_137), B_138) | ~r1_tarski(B_139, B_138) | ~r1_tarski(A_136, B_139) | r1_tarski(A_136, B_137))), inference(resolution, [status(thm)], [c_137, c_2])).
% 4.50/1.81  tff(c_446, plain, (![A_140, B_141]: (r2_hidden('#skF_1'(A_140, B_141), k2_zfmisc_1('#skF_3', '#skF_4')) | ~r1_tarski(A_140, '#skF_6') | r1_tarski(A_140, B_141))), inference(resolution, [status(thm)], [c_64, c_432])).
% 4.50/1.81  tff(c_457, plain, (![A_140]: (~r1_tarski(A_140, '#skF_6') | r1_tarski(A_140, k2_zfmisc_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_446, c_4])).
% 4.50/1.81  tff(c_30, plain, (![A_19, B_20, C_21]: (r2_hidden('#skF_2'(A_19, B_20, C_21), k1_relat_1(C_21)) | ~r2_hidden(A_19, k9_relat_1(C_21, B_20)) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.50/1.81  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.50/1.81  tff(c_366, plain, (![A_126, B_127, C_128]: (r2_hidden(k4_tarski('#skF_2'(A_126, B_127, C_128), A_126), C_128) | ~r2_hidden(A_126, k9_relat_1(C_128, B_127)) | ~v1_relat_1(C_128))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.50/1.81  tff(c_34, plain, (![C_27, A_25, B_26]: (k1_funct_1(C_27, A_25)=B_26 | ~r2_hidden(k4_tarski(A_25, B_26), C_27) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.50/1.81  tff(c_857, plain, (![C_196, A_197, B_198]: (k1_funct_1(C_196, '#skF_2'(A_197, B_198, C_196))=A_197 | ~v1_funct_1(C_196) | ~r2_hidden(A_197, k9_relat_1(C_196, B_198)) | ~v1_relat_1(C_196))), inference(resolution, [status(thm)], [c_366, c_34])).
% 4.50/1.81  tff(c_871, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_240, c_857])).
% 4.50/1.81  tff(c_887, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_48, c_871])).
% 4.50/1.81  tff(c_495, plain, (![A_145, C_146]: (r2_hidden(k4_tarski(A_145, k1_funct_1(C_146, A_145)), C_146) | ~r2_hidden(A_145, k1_relat_1(C_146)) | ~v1_funct_1(C_146) | ~v1_relat_1(C_146))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.50/1.81  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.50/1.81  tff(c_544, plain, (![A_145, C_146]: (m1_subset_1(k4_tarski(A_145, k1_funct_1(C_146, A_145)), C_146) | ~r2_hidden(A_145, k1_relat_1(C_146)) | ~v1_funct_1(C_146) | ~v1_relat_1(C_146))), inference(resolution, [status(thm)], [c_495, c_14])).
% 4.50/1.81  tff(c_894, plain, (m1_subset_1(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_887, c_544])).
% 4.50/1.81  tff(c_901, plain, (m1_subset_1(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_48, c_894])).
% 4.50/1.81  tff(c_906, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_901])).
% 4.50/1.81  tff(c_912, plain, (~r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_30, c_906])).
% 4.50/1.81  tff(c_919, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_240, c_912])).
% 4.50/1.81  tff(c_921, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_901])).
% 4.50/1.81  tff(c_32, plain, (![A_25, C_27]: (r2_hidden(k4_tarski(A_25, k1_funct_1(C_27, A_25)), C_27) | ~r2_hidden(A_25, k1_relat_1(C_27)) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.50/1.81  tff(c_897, plain, (r2_hidden(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_887, c_32])).
% 4.50/1.81  tff(c_903, plain, (r2_hidden(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_48, c_897])).
% 4.50/1.81  tff(c_1174, plain, (r2_hidden(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_921, c_903])).
% 4.50/1.81  tff(c_1201, plain, (![B_220]: (r2_hidden(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), B_220) | ~r1_tarski('#skF_6', B_220))), inference(resolution, [status(thm)], [c_1174, c_2])).
% 4.50/1.81  tff(c_12, plain, (![A_6, C_8, B_7, D_9]: (r2_hidden(A_6, C_8) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.50/1.81  tff(c_1558, plain, (![C_237, D_238]: (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), C_237) | ~r1_tarski('#skF_6', k2_zfmisc_1(C_237, D_238)))), inference(resolution, [status(thm)], [c_1201, c_12])).
% 4.50/1.81  tff(c_1561, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3') | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_457, c_1558])).
% 4.50/1.81  tff(c_1566, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_1561])).
% 4.50/1.81  tff(c_1576, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_1566, c_14])).
% 4.50/1.81  tff(c_1583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_352, c_1576])).
% 4.50/1.81  tff(c_1584, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7'), inference(splitRight, [status(thm)], [c_339])).
% 4.50/1.81  tff(c_1601, plain, (![A_247, B_248, C_249]: (r2_hidden(k4_tarski('#skF_2'(A_247, B_248, C_249), A_247), C_249) | ~r2_hidden(A_247, k9_relat_1(C_249, B_248)) | ~v1_relat_1(C_249))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.50/1.81  tff(c_2005, plain, (![C_306, A_307, B_308]: (k1_funct_1(C_306, '#skF_2'(A_307, B_308, C_306))=A_307 | ~v1_funct_1(C_306) | ~r2_hidden(A_307, k9_relat_1(C_306, B_308)) | ~v1_relat_1(C_306))), inference(resolution, [status(thm)], [c_1601, c_34])).
% 4.50/1.81  tff(c_2016, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_240, c_2005])).
% 4.50/1.81  tff(c_2031, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_48, c_2016])).
% 4.50/1.81  tff(c_2033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1584, c_2031])).
% 4.50/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.81  
% 4.50/1.81  Inference rules
% 4.50/1.81  ----------------------
% 4.50/1.81  #Ref     : 0
% 4.50/1.81  #Sup     : 432
% 4.50/1.81  #Fact    : 0
% 4.50/1.81  #Define  : 0
% 4.50/1.81  #Split   : 11
% 4.50/1.81  #Chain   : 0
% 4.50/1.81  #Close   : 0
% 4.50/1.81  
% 4.50/1.81  Ordering : KBO
% 4.50/1.81  
% 4.50/1.81  Simplification rules
% 4.50/1.81  ----------------------
% 4.50/1.81  #Subsume      : 23
% 4.50/1.81  #Demod        : 64
% 4.50/1.81  #Tautology    : 30
% 4.50/1.81  #SimpNegUnit  : 2
% 4.50/1.81  #BackRed      : 3
% 4.50/1.81  
% 4.50/1.81  #Partial instantiations: 0
% 4.50/1.81  #Strategies tried      : 1
% 4.50/1.81  
% 4.50/1.81  Timing (in seconds)
% 4.50/1.81  ----------------------
% 4.50/1.81  Preprocessing        : 0.34
% 4.50/1.81  Parsing              : 0.18
% 4.50/1.81  CNF conversion       : 0.03
% 4.50/1.81  Main loop            : 0.64
% 4.50/1.81  Inferencing          : 0.23
% 4.50/1.81  Reduction            : 0.18
% 4.50/1.82  Demodulation         : 0.12
% 4.50/1.82  BG Simplification    : 0.03
% 4.50/1.82  Subsumption          : 0.15
% 4.50/1.82  Abstraction          : 0.03
% 4.50/1.82  MUC search           : 0.00
% 4.50/1.82  Cooper               : 0.00
% 4.50/1.82  Total                : 1.02
% 4.50/1.82  Index Insertion      : 0.00
% 4.50/1.82  Index Deletion       : 0.00
% 4.50/1.82  Index Matching       : 0.00
% 4.50/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
