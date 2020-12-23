%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0830+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:54 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 208 expanded)
%              Number of leaves         :   30 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :  129 ( 488 expanded)
%              Number of equality atoms :    4 (  13 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_56,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_65,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_44,c_56])).

tff(c_28,plain,(
    ! [A_40,B_41] :
      ( v1_relat_1(k7_relat_1(A_40,B_41))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [A_23,B_33] :
      ( r2_hidden(k4_tarski('#skF_5'(A_23,B_33),'#skF_6'(A_23,B_33)),A_23)
      | r1_tarski(A_23,B_33)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_154,plain,(
    ! [D_94,B_95,E_96,A_97] :
      ( r2_hidden(D_94,B_95)
      | ~ r2_hidden(k4_tarski(D_94,E_96),k7_relat_1(A_97,B_95))
      | ~ v1_relat_1(k7_relat_1(A_97,B_95))
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_159,plain,(
    ! [A_97,B_95,B_33] :
      ( r2_hidden('#skF_5'(k7_relat_1(A_97,B_95),B_33),B_95)
      | ~ v1_relat_1(A_97)
      | r1_tarski(k7_relat_1(A_97,B_95),B_33)
      | ~ v1_relat_1(k7_relat_1(A_97,B_95)) ) ),
    inference(resolution,[status(thm)],[c_26,c_154])).

tff(c_46,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_50,plain,(
    r1_tarski('#skF_10',k2_zfmisc_1('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_44,c_46])).

tff(c_147,plain,(
    ! [C_90,D_91,B_92,A_93] :
      ( r2_hidden(k4_tarski(C_90,D_91),B_92)
      | ~ r2_hidden(k4_tarski(C_90,D_91),A_93)
      | ~ r1_tarski(A_93,B_92)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_169,plain,(
    ! [A_111,B_112,B_113] :
      ( r2_hidden(k4_tarski('#skF_5'(A_111,B_112),'#skF_6'(A_111,B_112)),B_113)
      | ~ r1_tarski(A_111,B_113)
      | r1_tarski(A_111,B_112)
      | ~ v1_relat_1(A_111) ) ),
    inference(resolution,[status(thm)],[c_26,c_147])).

tff(c_22,plain,(
    ! [C_38,D_39,B_33,A_23] :
      ( r2_hidden(k4_tarski(C_38,D_39),B_33)
      | ~ r2_hidden(k4_tarski(C_38,D_39),A_23)
      | ~ r1_tarski(A_23,B_33)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_343,plain,(
    ! [A_153,B_154,B_155,B_156] :
      ( r2_hidden(k4_tarski('#skF_5'(A_153,B_154),'#skF_6'(A_153,B_154)),B_155)
      | ~ r1_tarski(B_156,B_155)
      | ~ v1_relat_1(B_156)
      | ~ r1_tarski(A_153,B_156)
      | r1_tarski(A_153,B_154)
      | ~ v1_relat_1(A_153) ) ),
    inference(resolution,[status(thm)],[c_169,c_22])).

tff(c_347,plain,(
    ! [A_153,B_154] :
      ( r2_hidden(k4_tarski('#skF_5'(A_153,B_154),'#skF_6'(A_153,B_154)),k2_zfmisc_1('#skF_7','#skF_9'))
      | ~ v1_relat_1('#skF_10')
      | ~ r1_tarski(A_153,'#skF_10')
      | r1_tarski(A_153,B_154)
      | ~ v1_relat_1(A_153) ) ),
    inference(resolution,[status(thm)],[c_50,c_343])).

tff(c_352,plain,(
    ! [A_157,B_158] :
      ( r2_hidden(k4_tarski('#skF_5'(A_157,B_158),'#skF_6'(A_157,B_158)),k2_zfmisc_1('#skF_7','#skF_9'))
      | ~ r1_tarski(A_157,'#skF_10')
      | r1_tarski(A_157,B_158)
      | ~ v1_relat_1(A_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_347])).

tff(c_34,plain,(
    ! [B_47,D_49,A_46,C_48] :
      ( r2_hidden(B_47,D_49)
      | ~ r2_hidden(k4_tarski(A_46,B_47),k2_zfmisc_1(C_48,D_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_390,plain,(
    ! [A_160,B_161] :
      ( r2_hidden('#skF_6'(A_160,B_161),'#skF_9')
      | ~ r1_tarski(A_160,'#skF_10')
      | r1_tarski(A_160,B_161)
      | ~ v1_relat_1(A_160) ) ),
    inference(resolution,[status(thm)],[c_352,c_34])).

tff(c_32,plain,(
    ! [A_46,B_47,C_48,D_49] :
      ( r2_hidden(k4_tarski(A_46,B_47),k2_zfmisc_1(C_48,D_49))
      | ~ r2_hidden(B_47,D_49)
      | ~ r2_hidden(A_46,C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_106,plain,(
    ! [A_81,B_82] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_81,B_82),'#skF_6'(A_81,B_82)),B_82)
      | r1_tarski(A_81,B_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_111,plain,(
    ! [A_81,C_48,D_49] :
      ( r1_tarski(A_81,k2_zfmisc_1(C_48,D_49))
      | ~ v1_relat_1(A_81)
      | ~ r2_hidden('#skF_6'(A_81,k2_zfmisc_1(C_48,D_49)),D_49)
      | ~ r2_hidden('#skF_5'(A_81,k2_zfmisc_1(C_48,D_49)),C_48) ) ),
    inference(resolution,[status(thm)],[c_32,c_106])).

tff(c_476,plain,(
    ! [A_173,C_174] :
      ( ~ r2_hidden('#skF_5'(A_173,k2_zfmisc_1(C_174,'#skF_9')),C_174)
      | ~ r1_tarski(A_173,'#skF_10')
      | r1_tarski(A_173,k2_zfmisc_1(C_174,'#skF_9'))
      | ~ v1_relat_1(A_173) ) ),
    inference(resolution,[status(thm)],[c_390,c_111])).

tff(c_594,plain,(
    ! [A_186,B_187] :
      ( ~ r1_tarski(k7_relat_1(A_186,B_187),'#skF_10')
      | ~ v1_relat_1(A_186)
      | r1_tarski(k7_relat_1(A_186,B_187),k2_zfmisc_1(B_187,'#skF_9'))
      | ~ v1_relat_1(k7_relat_1(A_186,B_187)) ) ),
    inference(resolution,[status(thm)],[c_159,c_476])).

tff(c_87,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k5_relset_1(A_76,B_77,C_78,D_79) = k7_relat_1(C_78,D_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_94,plain,(
    ! [D_79] : k5_relset_1('#skF_7','#skF_9','#skF_10',D_79) = k7_relat_1('#skF_10',D_79) ),
    inference(resolution,[status(thm)],[c_44,c_87])).

tff(c_40,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(A_50,k1_zfmisc_1(B_51))
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_42,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_7','#skF_9','#skF_10','#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_75,plain,(
    ~ r1_tarski(k5_relset_1('#skF_7','#skF_9','#skF_10','#skF_8'),k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_40,c_42])).

tff(c_95,plain,(
    ~ r1_tarski(k7_relat_1('#skF_10','#skF_8'),k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_75])).

tff(c_605,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_10','#skF_8'),'#skF_10')
    | ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1(k7_relat_1('#skF_10','#skF_8')) ),
    inference(resolution,[status(thm)],[c_594,c_95])).

tff(c_615,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_10','#skF_8'),'#skF_10')
    | ~ v1_relat_1(k7_relat_1('#skF_10','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_605])).

tff(c_617,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_10','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_615])).

tff(c_620,plain,(
    ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_28,c_617])).

tff(c_624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_620])).

tff(c_626,plain,(
    v1_relat_1(k7_relat_1('#skF_10','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_615])).

tff(c_162,plain,(
    ! [D_104,E_105,A_106,B_107] :
      ( r2_hidden(k4_tarski(D_104,E_105),A_106)
      | ~ r2_hidden(k4_tarski(D_104,E_105),k7_relat_1(A_106,B_107))
      | ~ v1_relat_1(k7_relat_1(A_106,B_107))
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1321,plain,(
    ! [A_259,B_260,B_261] :
      ( r2_hidden(k4_tarski('#skF_5'(k7_relat_1(A_259,B_260),B_261),'#skF_6'(k7_relat_1(A_259,B_260),B_261)),A_259)
      | ~ v1_relat_1(A_259)
      | r1_tarski(k7_relat_1(A_259,B_260),B_261)
      | ~ v1_relat_1(k7_relat_1(A_259,B_260)) ) ),
    inference(resolution,[status(thm)],[c_26,c_162])).

tff(c_24,plain,(
    ! [A_23,B_33] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_23,B_33),'#skF_6'(A_23,B_33)),B_33)
      | r1_tarski(A_23,B_33)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1388,plain,(
    ! [A_262,B_263] :
      ( ~ v1_relat_1(A_262)
      | r1_tarski(k7_relat_1(A_262,B_263),A_262)
      | ~ v1_relat_1(k7_relat_1(A_262,B_263)) ) ),
    inference(resolution,[status(thm)],[c_1321,c_24])).

tff(c_625,plain,(
    ~ r1_tarski(k7_relat_1('#skF_10','#skF_8'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_615])).

tff(c_1403,plain,
    ( ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1(k7_relat_1('#skF_10','#skF_8')) ),
    inference(resolution,[status(thm)],[c_1388,c_625])).

tff(c_1437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_626,c_65,c_1403])).

%------------------------------------------------------------------------------
