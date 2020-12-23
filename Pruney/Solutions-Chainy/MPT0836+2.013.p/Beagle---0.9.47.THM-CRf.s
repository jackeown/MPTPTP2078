%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:04 EST 2020

% Result     : Theorem 9.64s
% Output     : CNFRefutation 9.73s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 142 expanded)
%              Number of leaves         :   29 (  62 expanded)
%              Depth                    :    7
%              Number of atoms          :  121 ( 323 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => ( r2_hidden(D,k1_relset_1(A,B,C))
                    <=> ? [E] :
                          ( m1_subset_1(E,B)
                          & r2_hidden(k4_tarski(D,E),C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_36,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5413,plain,(
    ! [A_483,B_484,C_485] :
      ( k1_relset_1(A_483,B_484,C_485) = k1_relat_1(C_485)
      | ~ m1_subset_1(C_485,k1_zfmisc_1(k2_zfmisc_1(A_483,B_484))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5432,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_5413])).

tff(c_276,plain,(
    ! [A_130,B_131,C_132] :
      ( k1_relset_1(A_130,B_131,C_132) = k1_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_290,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_276])).

tff(c_66,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_1'(A_86,B_87),A_86)
      | r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    ! [A_86] : r1_tarski(A_86,A_86) ),
    inference(resolution,[status(thm)],[c_66,c_4])).

tff(c_52,plain,
    ( r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8'))
    | m1_subset_1('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_65,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_48,plain,
    ( r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8'))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_92,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_101,plain,(
    ! [B_2] :
      ( r2_hidden(k4_tarski('#skF_9','#skF_10'),B_2)
      | ~ r1_tarski('#skF_8',B_2) ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_22,plain,(
    ! [C_29,A_14,D_32] :
      ( r2_hidden(C_29,k1_relat_1(A_14))
      | ~ r2_hidden(k4_tarski(C_29,D_32),A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_102,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_92,c_22])).

tff(c_111,plain,(
    ! [A_107,B_108,C_109] :
      ( k1_relset_1(A_107,B_108,C_109) = k1_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_125,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_111])).

tff(c_42,plain,(
    ! [E_77] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_77),'#skF_8')
      | ~ m1_subset_1(E_77,'#skF_7')
      | ~ r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_235,plain,(
    ! [E_125] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_125),'#skF_8')
      | ~ m1_subset_1(E_125,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_125,c_42])).

tff(c_239,plain,
    ( ~ m1_subset_1('#skF_10','#skF_7')
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_101,c_235])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_65,c_239])).

tff(c_247,plain,(
    r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_293,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_247])).

tff(c_55,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(A_82,B_83)
      | ~ m1_subset_1(A_82,k1_zfmisc_1(B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_63,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_36,c_55])).

tff(c_351,plain,(
    ! [C_143,A_144] :
      ( r2_hidden(k4_tarski(C_143,'#skF_5'(A_144,k1_relat_1(A_144),C_143)),A_144)
      | ~ r2_hidden(C_143,k1_relat_1(A_144)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1308,plain,(
    ! [C_263,A_264,B_265] :
      ( r2_hidden(k4_tarski(C_263,'#skF_5'(A_264,k1_relat_1(A_264),C_263)),B_265)
      | ~ r1_tarski(A_264,B_265)
      | ~ r2_hidden(C_263,k1_relat_1(A_264)) ) ),
    inference(resolution,[status(thm)],[c_351,c_2])).

tff(c_10,plain,(
    ! [B_7,D_9,A_6,C_8] :
      ( r2_hidden(B_7,D_9)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5277,plain,(
    ! [A_448,C_449,D_450,C_451] :
      ( r2_hidden('#skF_5'(A_448,k1_relat_1(A_448),C_449),D_450)
      | ~ r1_tarski(A_448,k2_zfmisc_1(C_451,D_450))
      | ~ r2_hidden(C_449,k1_relat_1(A_448)) ) ),
    inference(resolution,[status(thm)],[c_1308,c_10])).

tff(c_5324,plain,(
    ! [C_452] :
      ( r2_hidden('#skF_5'('#skF_8',k1_relat_1('#skF_8'),C_452),'#skF_7')
      | ~ r2_hidden(C_452,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_63,c_5277])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_5338,plain,(
    ! [C_453] :
      ( m1_subset_1('#skF_5'('#skF_8',k1_relat_1('#skF_8'),C_453),'#skF_7')
      | ~ r2_hidden(C_453,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_5324,c_14])).

tff(c_248,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [E_77] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_77),'#skF_8')
      | ~ m1_subset_1(E_77,'#skF_7')
      | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_306,plain,(
    ! [E_77] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_77),'#skF_8')
      | ~ m1_subset_1(E_77,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_248,c_46])).

tff(c_1355,plain,(
    ! [A_264] :
      ( ~ m1_subset_1('#skF_5'(A_264,k1_relat_1(A_264),'#skF_9'),'#skF_7')
      | ~ r1_tarski(A_264,'#skF_8')
      | ~ r2_hidden('#skF_9',k1_relat_1(A_264)) ) ),
    inference(resolution,[status(thm)],[c_1308,c_306])).

tff(c_5342,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_5338,c_1355])).

tff(c_5349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_74,c_5342])).

tff(c_5350,plain,(
    r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_5455,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5432,c_5350])).

tff(c_5358,plain,(
    ! [A_455,B_456] :
      ( r2_hidden('#skF_1'(A_455,B_456),A_455)
      | r1_tarski(A_455,B_456) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5366,plain,(
    ! [A_455] : r1_tarski(A_455,A_455) ),
    inference(resolution,[status(thm)],[c_5358,c_4])).

tff(c_5513,plain,(
    ! [C_500,A_501] :
      ( r2_hidden(k4_tarski(C_500,'#skF_5'(A_501,k1_relat_1(A_501),C_500)),A_501)
      | ~ r2_hidden(C_500,k1_relat_1(A_501)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6907,plain,(
    ! [C_625,A_626,B_627] :
      ( r2_hidden(k4_tarski(C_625,'#skF_5'(A_626,k1_relat_1(A_626),C_625)),B_627)
      | ~ r1_tarski(A_626,B_627)
      | ~ r2_hidden(C_625,k1_relat_1(A_626)) ) ),
    inference(resolution,[status(thm)],[c_5513,c_2])).

tff(c_11909,plain,(
    ! [A_841,C_842,D_843,C_844] :
      ( r2_hidden('#skF_5'(A_841,k1_relat_1(A_841),C_842),D_843)
      | ~ r1_tarski(A_841,k2_zfmisc_1(C_844,D_843))
      | ~ r2_hidden(C_842,k1_relat_1(A_841)) ) ),
    inference(resolution,[status(thm)],[c_6907,c_10])).

tff(c_11948,plain,(
    ! [C_845] :
      ( r2_hidden('#skF_5'('#skF_8',k1_relat_1('#skF_8'),C_845),'#skF_7')
      | ~ r2_hidden(C_845,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_63,c_11909])).

tff(c_11971,plain,(
    ! [C_846] :
      ( m1_subset_1('#skF_5'('#skF_8',k1_relat_1('#skF_8'),C_846),'#skF_7')
      | ~ r2_hidden(C_846,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_11948,c_14])).

tff(c_5351,plain,(
    ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,(
    ! [E_77] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_77),'#skF_8')
      | ~ m1_subset_1(E_77,'#skF_7')
      | m1_subset_1('#skF_10','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5352,plain,(
    ! [E_77] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_77),'#skF_8')
      | ~ m1_subset_1(E_77,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_5351,c_50])).

tff(c_6963,plain,(
    ! [A_626] :
      ( ~ m1_subset_1('#skF_5'(A_626,k1_relat_1(A_626),'#skF_9'),'#skF_7')
      | ~ r1_tarski(A_626,'#skF_8')
      | ~ r2_hidden('#skF_9',k1_relat_1(A_626)) ) ),
    inference(resolution,[status(thm)],[c_6907,c_5352])).

tff(c_11975,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_11971,c_6963])).

tff(c_11982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5455,c_5366,c_11975])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.64/3.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.64/3.40  
% 9.64/3.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.64/3.41  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 9.64/3.41  
% 9.64/3.41  %Foreground sorts:
% 9.64/3.41  
% 9.64/3.41  
% 9.64/3.41  %Background operators:
% 9.64/3.41  
% 9.64/3.41  
% 9.64/3.41  %Foreground operators:
% 9.64/3.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.64/3.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.64/3.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.64/3.41  tff('#skF_7', type, '#skF_7': $i).
% 9.64/3.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.64/3.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.64/3.41  tff('#skF_10', type, '#skF_10': $i).
% 9.64/3.41  tff('#skF_6', type, '#skF_6': $i).
% 9.64/3.41  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 9.64/3.41  tff('#skF_9', type, '#skF_9': $i).
% 9.64/3.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.64/3.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.64/3.41  tff('#skF_8', type, '#skF_8': $i).
% 9.64/3.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.64/3.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.64/3.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.64/3.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.64/3.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.64/3.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.64/3.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.64/3.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.64/3.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.64/3.41  
% 9.73/3.42  tff(f_79, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, A) => (r2_hidden(D, k1_relset_1(A, B, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(D, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relset_1)).
% 9.73/3.42  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.73/3.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.73/3.42  tff(f_54, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 9.73/3.42  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.73/3.42  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 9.73/3.42  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 9.73/3.42  tff(c_36, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.73/3.42  tff(c_5413, plain, (![A_483, B_484, C_485]: (k1_relset_1(A_483, B_484, C_485)=k1_relat_1(C_485) | ~m1_subset_1(C_485, k1_zfmisc_1(k2_zfmisc_1(A_483, B_484))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.73/3.42  tff(c_5432, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_5413])).
% 9.73/3.42  tff(c_276, plain, (![A_130, B_131, C_132]: (k1_relset_1(A_130, B_131, C_132)=k1_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.73/3.42  tff(c_290, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_276])).
% 9.73/3.42  tff(c_66, plain, (![A_86, B_87]: (r2_hidden('#skF_1'(A_86, B_87), A_86) | r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.73/3.42  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.73/3.42  tff(c_74, plain, (![A_86]: (r1_tarski(A_86, A_86))), inference(resolution, [status(thm)], [c_66, c_4])).
% 9.73/3.42  tff(c_52, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')) | m1_subset_1('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.73/3.42  tff(c_65, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(splitLeft, [status(thm)], [c_52])).
% 9.73/3.42  tff(c_48, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.73/3.42  tff(c_92, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(splitLeft, [status(thm)], [c_48])).
% 9.73/3.42  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.73/3.42  tff(c_101, plain, (![B_2]: (r2_hidden(k4_tarski('#skF_9', '#skF_10'), B_2) | ~r1_tarski('#skF_8', B_2))), inference(resolution, [status(thm)], [c_92, c_2])).
% 9.73/3.42  tff(c_22, plain, (![C_29, A_14, D_32]: (r2_hidden(C_29, k1_relat_1(A_14)) | ~r2_hidden(k4_tarski(C_29, D_32), A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.73/3.42  tff(c_102, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_92, c_22])).
% 9.73/3.42  tff(c_111, plain, (![A_107, B_108, C_109]: (k1_relset_1(A_107, B_108, C_109)=k1_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.73/3.42  tff(c_125, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_111])).
% 9.73/3.42  tff(c_42, plain, (![E_77]: (~r2_hidden(k4_tarski('#skF_9', E_77), '#skF_8') | ~m1_subset_1(E_77, '#skF_7') | ~r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.73/3.42  tff(c_235, plain, (![E_125]: (~r2_hidden(k4_tarski('#skF_9', E_125), '#skF_8') | ~m1_subset_1(E_125, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_125, c_42])).
% 9.73/3.42  tff(c_239, plain, (~m1_subset_1('#skF_10', '#skF_7') | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_101, c_235])).
% 9.73/3.42  tff(c_246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_65, c_239])).
% 9.73/3.42  tff(c_247, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_48])).
% 9.73/3.42  tff(c_293, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_290, c_247])).
% 9.73/3.42  tff(c_55, plain, (![A_82, B_83]: (r1_tarski(A_82, B_83) | ~m1_subset_1(A_82, k1_zfmisc_1(B_83)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.73/3.42  tff(c_63, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_36, c_55])).
% 9.73/3.42  tff(c_351, plain, (![C_143, A_144]: (r2_hidden(k4_tarski(C_143, '#skF_5'(A_144, k1_relat_1(A_144), C_143)), A_144) | ~r2_hidden(C_143, k1_relat_1(A_144)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.73/3.42  tff(c_1308, plain, (![C_263, A_264, B_265]: (r2_hidden(k4_tarski(C_263, '#skF_5'(A_264, k1_relat_1(A_264), C_263)), B_265) | ~r1_tarski(A_264, B_265) | ~r2_hidden(C_263, k1_relat_1(A_264)))), inference(resolution, [status(thm)], [c_351, c_2])).
% 9.73/3.42  tff(c_10, plain, (![B_7, D_9, A_6, C_8]: (r2_hidden(B_7, D_9) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.73/3.42  tff(c_5277, plain, (![A_448, C_449, D_450, C_451]: (r2_hidden('#skF_5'(A_448, k1_relat_1(A_448), C_449), D_450) | ~r1_tarski(A_448, k2_zfmisc_1(C_451, D_450)) | ~r2_hidden(C_449, k1_relat_1(A_448)))), inference(resolution, [status(thm)], [c_1308, c_10])).
% 9.73/3.42  tff(c_5324, plain, (![C_452]: (r2_hidden('#skF_5'('#skF_8', k1_relat_1('#skF_8'), C_452), '#skF_7') | ~r2_hidden(C_452, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_63, c_5277])).
% 9.73/3.42  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.73/3.42  tff(c_5338, plain, (![C_453]: (m1_subset_1('#skF_5'('#skF_8', k1_relat_1('#skF_8'), C_453), '#skF_7') | ~r2_hidden(C_453, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_5324, c_14])).
% 9.73/3.42  tff(c_248, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(splitRight, [status(thm)], [c_48])).
% 9.73/3.42  tff(c_46, plain, (![E_77]: (~r2_hidden(k4_tarski('#skF_9', E_77), '#skF_8') | ~m1_subset_1(E_77, '#skF_7') | r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.73/3.42  tff(c_306, plain, (![E_77]: (~r2_hidden(k4_tarski('#skF_9', E_77), '#skF_8') | ~m1_subset_1(E_77, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_248, c_46])).
% 9.73/3.42  tff(c_1355, plain, (![A_264]: (~m1_subset_1('#skF_5'(A_264, k1_relat_1(A_264), '#skF_9'), '#skF_7') | ~r1_tarski(A_264, '#skF_8') | ~r2_hidden('#skF_9', k1_relat_1(A_264)))), inference(resolution, [status(thm)], [c_1308, c_306])).
% 9.73/3.42  tff(c_5342, plain, (~r1_tarski('#skF_8', '#skF_8') | ~r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_5338, c_1355])).
% 9.73/3.42  tff(c_5349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_293, c_74, c_5342])).
% 9.73/3.42  tff(c_5350, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_52])).
% 9.73/3.42  tff(c_5455, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_5432, c_5350])).
% 9.73/3.42  tff(c_5358, plain, (![A_455, B_456]: (r2_hidden('#skF_1'(A_455, B_456), A_455) | r1_tarski(A_455, B_456))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.73/3.42  tff(c_5366, plain, (![A_455]: (r1_tarski(A_455, A_455))), inference(resolution, [status(thm)], [c_5358, c_4])).
% 9.73/3.42  tff(c_5513, plain, (![C_500, A_501]: (r2_hidden(k4_tarski(C_500, '#skF_5'(A_501, k1_relat_1(A_501), C_500)), A_501) | ~r2_hidden(C_500, k1_relat_1(A_501)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.73/3.42  tff(c_6907, plain, (![C_625, A_626, B_627]: (r2_hidden(k4_tarski(C_625, '#skF_5'(A_626, k1_relat_1(A_626), C_625)), B_627) | ~r1_tarski(A_626, B_627) | ~r2_hidden(C_625, k1_relat_1(A_626)))), inference(resolution, [status(thm)], [c_5513, c_2])).
% 9.73/3.42  tff(c_11909, plain, (![A_841, C_842, D_843, C_844]: (r2_hidden('#skF_5'(A_841, k1_relat_1(A_841), C_842), D_843) | ~r1_tarski(A_841, k2_zfmisc_1(C_844, D_843)) | ~r2_hidden(C_842, k1_relat_1(A_841)))), inference(resolution, [status(thm)], [c_6907, c_10])).
% 9.73/3.42  tff(c_11948, plain, (![C_845]: (r2_hidden('#skF_5'('#skF_8', k1_relat_1('#skF_8'), C_845), '#skF_7') | ~r2_hidden(C_845, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_63, c_11909])).
% 9.73/3.42  tff(c_11971, plain, (![C_846]: (m1_subset_1('#skF_5'('#skF_8', k1_relat_1('#skF_8'), C_846), '#skF_7') | ~r2_hidden(C_846, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_11948, c_14])).
% 9.73/3.42  tff(c_5351, plain, (~m1_subset_1('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_52])).
% 9.73/3.42  tff(c_50, plain, (![E_77]: (~r2_hidden(k4_tarski('#skF_9', E_77), '#skF_8') | ~m1_subset_1(E_77, '#skF_7') | m1_subset_1('#skF_10', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.73/3.42  tff(c_5352, plain, (![E_77]: (~r2_hidden(k4_tarski('#skF_9', E_77), '#skF_8') | ~m1_subset_1(E_77, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_5351, c_50])).
% 9.73/3.42  tff(c_6963, plain, (![A_626]: (~m1_subset_1('#skF_5'(A_626, k1_relat_1(A_626), '#skF_9'), '#skF_7') | ~r1_tarski(A_626, '#skF_8') | ~r2_hidden('#skF_9', k1_relat_1(A_626)))), inference(resolution, [status(thm)], [c_6907, c_5352])).
% 9.73/3.42  tff(c_11975, plain, (~r1_tarski('#skF_8', '#skF_8') | ~r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_11971, c_6963])).
% 9.73/3.42  tff(c_11982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5455, c_5366, c_11975])).
% 9.73/3.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.73/3.42  
% 9.73/3.42  Inference rules
% 9.73/3.42  ----------------------
% 9.73/3.42  #Ref     : 0
% 9.73/3.42  #Sup     : 2836
% 9.73/3.42  #Fact    : 0
% 9.73/3.42  #Define  : 0
% 9.73/3.42  #Split   : 27
% 9.73/3.42  #Chain   : 0
% 9.73/3.42  #Close   : 0
% 9.73/3.42  
% 9.73/3.42  Ordering : KBO
% 9.73/3.42  
% 9.73/3.42  Simplification rules
% 9.73/3.42  ----------------------
% 9.73/3.42  #Subsume      : 433
% 9.73/3.42  #Demod        : 215
% 9.73/3.42  #Tautology    : 215
% 9.73/3.42  #SimpNegUnit  : 10
% 9.73/3.42  #BackRed      : 49
% 9.73/3.42  
% 9.73/3.42  #Partial instantiations: 0
% 9.73/3.42  #Strategies tried      : 1
% 9.73/3.42  
% 9.73/3.42  Timing (in seconds)
% 9.73/3.42  ----------------------
% 9.73/3.43  Preprocessing        : 0.29
% 9.73/3.43  Parsing              : 0.15
% 9.73/3.43  CNF conversion       : 0.03
% 9.73/3.43  Main loop            : 2.31
% 9.73/3.43  Inferencing          : 0.68
% 9.73/3.43  Reduction            : 0.61
% 9.73/3.43  Demodulation         : 0.40
% 9.73/3.43  BG Simplification    : 0.08
% 9.73/3.43  Subsumption          : 0.71
% 9.73/3.43  Abstraction          : 0.12
% 9.73/3.43  MUC search           : 0.00
% 9.73/3.43  Cooper               : 0.00
% 9.73/3.43  Total                : 2.65
% 9.73/3.43  Index Insertion      : 0.00
% 9.73/3.43  Index Deletion       : 0.00
% 9.73/3.43  Index Matching       : 0.00
% 9.73/3.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
