%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:08 EST 2020

% Result     : Theorem 10.60s
% Output     : CNFRefutation 10.67s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 196 expanded)
%              Number of leaves         :   30 (  80 expanded)
%              Depth                    :    9
%              Number of atoms          :  154 ( 438 expanded)
%              Number of equality atoms :    6 (  25 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ! [D] :
                    ( r2_hidden(D,k2_relset_1(B,A,C))
                  <=> ? [E] :
                        ( m1_subset_1(E,B)
                        & r2_hidden(k4_tarski(E,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_34,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_7334,plain,(
    ! [A_521,B_522,C_523] :
      ( k2_relset_1(A_521,B_522,C_523) = k2_relat_1(C_523)
      | ~ m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1(A_521,B_522))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_7348,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_7334])).

tff(c_50,plain,
    ( m1_subset_1('#skF_10','#skF_7')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_69,plain,(
    r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_7352,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7348,c_69])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [A_85,B_86] :
      ( ~ r2_hidden('#skF_1'(A_85,B_86),B_86)
      | r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_52,plain,(
    ! [A_81,B_82] :
      ( r1_tarski(A_81,B_82)
      | ~ m1_subset_1(A_81,k1_zfmisc_1(B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_60,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_52])).

tff(c_11870,plain,(
    ! [A_833,C_834] :
      ( r2_hidden(k4_tarski('#skF_5'(A_833,k2_relat_1(A_833),C_834),C_834),A_833)
      | ~ r2_hidden(C_834,k2_relat_1(A_833)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12933,plain,(
    ! [A_943,C_944,B_945] :
      ( r2_hidden(k4_tarski('#skF_5'(A_943,k2_relat_1(A_943),C_944),C_944),B_945)
      | ~ r1_tarski(A_943,B_945)
      | ~ r2_hidden(C_944,k2_relat_1(A_943)) ) ),
    inference(resolution,[status(thm)],[c_11870,c_2])).

tff(c_12,plain,(
    ! [A_6,C_8,B_7,D_9] :
      ( r2_hidden(A_6,C_8)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16973,plain,(
    ! [A_1161,C_1162,C_1163,D_1164] :
      ( r2_hidden('#skF_5'(A_1161,k2_relat_1(A_1161),C_1162),C_1163)
      | ~ r1_tarski(A_1161,k2_zfmisc_1(C_1163,D_1164))
      | ~ r2_hidden(C_1162,k2_relat_1(A_1161)) ) ),
    inference(resolution,[status(thm)],[c_12933,c_12])).

tff(c_17004,plain,(
    ! [C_1165] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_1165),'#skF_7')
      | ~ r2_hidden(C_1165,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_60,c_16973])).

tff(c_10,plain,(
    ! [B_7,D_9,A_6,C_8] :
      ( r2_hidden(B_7,D_9)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11966,plain,(
    ! [C_847,D_848,C_849] :
      ( r2_hidden(C_847,D_848)
      | ~ r2_hidden(C_847,k2_relat_1(k2_zfmisc_1(C_849,D_848))) ) ),
    inference(resolution,[status(thm)],[c_11870,c_10])).

tff(c_15303,plain,(
    ! [C_1084,D_1085,B_1086] :
      ( r2_hidden('#skF_1'(k2_relat_1(k2_zfmisc_1(C_1084,D_1085)),B_1086),D_1085)
      | r1_tarski(k2_relat_1(k2_zfmisc_1(C_1084,D_1085)),B_1086) ) ),
    inference(resolution,[status(thm)],[c_6,c_11966])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_15344,plain,(
    ! [C_1087,D_1088] : r1_tarski(k2_relat_1(k2_zfmisc_1(C_1087,D_1088)),D_1088) ),
    inference(resolution,[status(thm)],[c_15303,c_4])).

tff(c_7504,plain,(
    ! [A_551,C_552] :
      ( r2_hidden(k4_tarski('#skF_5'(A_551,k2_relat_1(A_551),C_552),C_552),A_551)
      | ~ r2_hidden(C_552,k2_relat_1(A_551)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8320,plain,(
    ! [A_642,C_643,B_644] :
      ( r2_hidden(k4_tarski('#skF_5'(A_642,k2_relat_1(A_642),C_643),C_643),B_644)
      | ~ r1_tarski(A_642,B_644)
      | ~ r2_hidden(C_643,k2_relat_1(A_642)) ) ),
    inference(resolution,[status(thm)],[c_7504,c_2])).

tff(c_11659,plain,(
    ! [A_816,C_817,C_818,D_819] :
      ( r2_hidden('#skF_5'(A_816,k2_relat_1(A_816),C_817),C_818)
      | ~ r1_tarski(A_816,k2_zfmisc_1(C_818,D_819))
      | ~ r2_hidden(C_817,k2_relat_1(A_816)) ) ),
    inference(resolution,[status(thm)],[c_8320,c_12])).

tff(c_11750,plain,(
    ! [C_821] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_821),'#skF_7')
      | ~ r2_hidden(C_821,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_60,c_11659])).

tff(c_7544,plain,(
    ! [C_556,D_557,C_558] :
      ( r2_hidden(C_556,D_557)
      | ~ r2_hidden(C_556,k2_relat_1(k2_zfmisc_1(C_558,D_557))) ) ),
    inference(resolution,[status(thm)],[c_7504,c_10])).

tff(c_8096,plain,(
    ! [C_615,D_616,B_617] :
      ( r2_hidden('#skF_1'(k2_relat_1(k2_zfmisc_1(C_615,D_616)),B_617),D_616)
      | r1_tarski(k2_relat_1(k2_zfmisc_1(C_615,D_616)),B_617) ) ),
    inference(resolution,[status(thm)],[c_6,c_7544])).

tff(c_8120,plain,(
    ! [C_618,D_619] : r1_tarski(k2_relat_1(k2_zfmisc_1(C_618,D_619)),D_619) ),
    inference(resolution,[status(thm)],[c_8096,c_4])).

tff(c_7407,plain,(
    ! [A_537,B_538,C_539,D_540] :
      ( r2_hidden(k4_tarski(A_537,B_538),k2_zfmisc_1(C_539,D_540))
      | ~ r2_hidden(B_538,D_540)
      | ~ r2_hidden(A_537,C_539) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ! [C_30,A_15,D_33] :
      ( r2_hidden(C_30,k2_relat_1(A_15))
      | ~ r2_hidden(k4_tarski(D_33,C_30),A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_7426,plain,(
    ! [B_541,C_542,D_543,A_544] :
      ( r2_hidden(B_541,k2_relat_1(k2_zfmisc_1(C_542,D_543)))
      | ~ r2_hidden(B_541,D_543)
      | ~ r2_hidden(A_544,C_542) ) ),
    inference(resolution,[status(thm)],[c_7407,c_22])).

tff(c_7439,plain,(
    ! [B_545,D_546] :
      ( r2_hidden(B_545,k2_relat_1(k2_zfmisc_1(k2_relat_1('#skF_8'),D_546)))
      | ~ r2_hidden(B_545,D_546) ) ),
    inference(resolution,[status(thm)],[c_7352,c_7426])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_85,plain,(
    ! [A_95,C_96,B_97] :
      ( m1_subset_1(A_95,C_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(C_96))
      | ~ r2_hidden(A_95,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_90,plain,(
    ! [A_95,B_11,A_10] :
      ( m1_subset_1(A_95,B_11)
      | ~ r2_hidden(A_95,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_85])).

tff(c_7460,plain,(
    ! [B_545,B_11,D_546] :
      ( m1_subset_1(B_545,B_11)
      | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(k2_relat_1('#skF_8'),D_546)),B_11)
      | ~ r2_hidden(B_545,D_546) ) ),
    inference(resolution,[status(thm)],[c_7439,c_90])).

tff(c_8146,plain,(
    ! [B_545,D_619] :
      ( m1_subset_1(B_545,D_619)
      | ~ r2_hidden(B_545,D_619) ) ),
    inference(resolution,[status(thm)],[c_8120,c_7460])).

tff(c_11767,plain,(
    ! [C_822] :
      ( m1_subset_1('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_822),'#skF_7')
      | ~ r2_hidden(C_822,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_11750,c_8146])).

tff(c_42,plain,(
    ! [E_78] :
      ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
      | ~ r2_hidden(k4_tarski(E_78,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_78,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_7363,plain,(
    ! [E_78] :
      ( ~ r2_hidden(k4_tarski(E_78,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_78,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_8366,plain,(
    ! [A_642] :
      ( ~ m1_subset_1('#skF_5'(A_642,k2_relat_1(A_642),'#skF_11'),'#skF_7')
      | ~ r1_tarski(A_642,'#skF_8')
      | ~ r2_hidden('#skF_11',k2_relat_1(A_642)) ) ),
    inference(resolution,[status(thm)],[c_8320,c_7363])).

tff(c_11771,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_11767,c_8366])).

tff(c_11778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7352,c_67,c_11771])).

tff(c_11779,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_11940,plain,(
    ! [A_842,B_843,C_844,D_845] :
      ( r2_hidden(k4_tarski(A_842,B_843),k2_zfmisc_1(C_844,D_845))
      | ~ r2_hidden(B_843,D_845)
      | ~ r2_hidden(A_842,C_844) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12249,plain,(
    ! [B_896,C_897,D_898,A_899] :
      ( r2_hidden(B_896,k2_relat_1(k2_zfmisc_1(C_897,D_898)))
      | ~ r2_hidden(B_896,D_898)
      | ~ r2_hidden(A_899,C_897) ) ),
    inference(resolution,[status(thm)],[c_11940,c_22])).

tff(c_12304,plain,(
    ! [B_900,D_901] :
      ( r2_hidden(B_900,k2_relat_1(k2_zfmisc_1('#skF_8',D_901)))
      | ~ r2_hidden(B_900,D_901) ) ),
    inference(resolution,[status(thm)],[c_11779,c_12249])).

tff(c_12337,plain,(
    ! [B_900,B_11,D_901] :
      ( m1_subset_1(B_900,B_11)
      | ~ r1_tarski(k2_relat_1(k2_zfmisc_1('#skF_8',D_901)),B_11)
      | ~ r2_hidden(B_900,D_901) ) ),
    inference(resolution,[status(thm)],[c_12304,c_90])).

tff(c_15448,plain,(
    ! [B_900,D_1088] :
      ( m1_subset_1(B_900,D_1088)
      | ~ r2_hidden(B_900,D_1088) ) ),
    inference(resolution,[status(thm)],[c_15344,c_12337])).

tff(c_17021,plain,(
    ! [C_1166] :
      ( m1_subset_1('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_1166),'#skF_7')
      | ~ r2_hidden(C_1166,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_17004,c_15448])).

tff(c_11789,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_11779,c_22])).

tff(c_40,plain,(
    ! [E_78] :
      ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(E_78,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_78,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_11825,plain,(
    ! [E_78] :
      ( ~ r2_hidden(k4_tarski(E_78,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_78,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11789,c_7348,c_40])).

tff(c_12972,plain,(
    ! [A_943] :
      ( ~ m1_subset_1('#skF_5'(A_943,k2_relat_1(A_943),'#skF_11'),'#skF_7')
      | ~ r1_tarski(A_943,'#skF_8')
      | ~ r2_hidden('#skF_11',k2_relat_1(A_943)) ) ),
    inference(resolution,[status(thm)],[c_12933,c_11825])).

tff(c_17025,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_17021,c_12972])).

tff(c_17032,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7352,c_67,c_17025])).

tff(c_17034,plain,(
    ~ r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_17055,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_17034,c_48])).

tff(c_17064,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_17055,c_22])).

tff(c_17107,plain,(
    ! [A_1191,B_1192,C_1193] :
      ( k2_relset_1(A_1191,B_1192,C_1193) = k2_relat_1(C_1193)
      | ~ m1_subset_1(C_1193,k1_zfmisc_1(k2_zfmisc_1(A_1191,B_1192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_17116,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_17107])).

tff(c_46,plain,
    ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_17066,plain,(
    ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_17034,c_46])).

tff(c_17117,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17116,c_17066])).

tff(c_17121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17064,c_17117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:37:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.60/3.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.60/3.87  
% 10.60/3.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.60/3.87  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 10.60/3.87  
% 10.60/3.87  %Foreground sorts:
% 10.60/3.87  
% 10.60/3.87  
% 10.60/3.87  %Background operators:
% 10.60/3.87  
% 10.60/3.87  
% 10.60/3.87  %Foreground operators:
% 10.60/3.87  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.60/3.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.60/3.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.60/3.87  tff('#skF_11', type, '#skF_11': $i).
% 10.60/3.87  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.60/3.87  tff('#skF_7', type, '#skF_7': $i).
% 10.60/3.87  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.60/3.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.60/3.87  tff('#skF_10', type, '#skF_10': $i).
% 10.60/3.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.60/3.87  tff('#skF_6', type, '#skF_6': $i).
% 10.60/3.87  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 10.60/3.87  tff('#skF_9', type, '#skF_9': $i).
% 10.60/3.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.60/3.87  tff('#skF_8', type, '#skF_8': $i).
% 10.60/3.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.60/3.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.60/3.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.60/3.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.60/3.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.60/3.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.60/3.87  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.60/3.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.60/3.87  
% 10.67/3.89  tff(f_79, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relset_1)).
% 10.67/3.89  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.67/3.89  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.67/3.89  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.67/3.89  tff(f_56, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 10.67/3.89  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 10.67/3.89  tff(f_48, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 10.67/3.89  tff(c_34, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.67/3.89  tff(c_7334, plain, (![A_521, B_522, C_523]: (k2_relset_1(A_521, B_522, C_523)=k2_relat_1(C_523) | ~m1_subset_1(C_523, k1_zfmisc_1(k2_zfmisc_1(A_521, B_522))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.67/3.89  tff(c_7348, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_7334])).
% 10.67/3.89  tff(c_50, plain, (m1_subset_1('#skF_10', '#skF_7') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.67/3.89  tff(c_69, plain, (r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_50])).
% 10.67/3.89  tff(c_7352, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_7348, c_69])).
% 10.67/3.89  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.67/3.89  tff(c_62, plain, (![A_85, B_86]: (~r2_hidden('#skF_1'(A_85, B_86), B_86) | r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.67/3.89  tff(c_67, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_62])).
% 10.67/3.89  tff(c_52, plain, (![A_81, B_82]: (r1_tarski(A_81, B_82) | ~m1_subset_1(A_81, k1_zfmisc_1(B_82)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.67/3.89  tff(c_60, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_52])).
% 10.67/3.89  tff(c_11870, plain, (![A_833, C_834]: (r2_hidden(k4_tarski('#skF_5'(A_833, k2_relat_1(A_833), C_834), C_834), A_833) | ~r2_hidden(C_834, k2_relat_1(A_833)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.67/3.89  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.67/3.89  tff(c_12933, plain, (![A_943, C_944, B_945]: (r2_hidden(k4_tarski('#skF_5'(A_943, k2_relat_1(A_943), C_944), C_944), B_945) | ~r1_tarski(A_943, B_945) | ~r2_hidden(C_944, k2_relat_1(A_943)))), inference(resolution, [status(thm)], [c_11870, c_2])).
% 10.67/3.89  tff(c_12, plain, (![A_6, C_8, B_7, D_9]: (r2_hidden(A_6, C_8) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.67/3.89  tff(c_16973, plain, (![A_1161, C_1162, C_1163, D_1164]: (r2_hidden('#skF_5'(A_1161, k2_relat_1(A_1161), C_1162), C_1163) | ~r1_tarski(A_1161, k2_zfmisc_1(C_1163, D_1164)) | ~r2_hidden(C_1162, k2_relat_1(A_1161)))), inference(resolution, [status(thm)], [c_12933, c_12])).
% 10.67/3.89  tff(c_17004, plain, (![C_1165]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_1165), '#skF_7') | ~r2_hidden(C_1165, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_60, c_16973])).
% 10.67/3.89  tff(c_10, plain, (![B_7, D_9, A_6, C_8]: (r2_hidden(B_7, D_9) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.67/3.89  tff(c_11966, plain, (![C_847, D_848, C_849]: (r2_hidden(C_847, D_848) | ~r2_hidden(C_847, k2_relat_1(k2_zfmisc_1(C_849, D_848))))), inference(resolution, [status(thm)], [c_11870, c_10])).
% 10.67/3.89  tff(c_15303, plain, (![C_1084, D_1085, B_1086]: (r2_hidden('#skF_1'(k2_relat_1(k2_zfmisc_1(C_1084, D_1085)), B_1086), D_1085) | r1_tarski(k2_relat_1(k2_zfmisc_1(C_1084, D_1085)), B_1086))), inference(resolution, [status(thm)], [c_6, c_11966])).
% 10.67/3.89  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.67/3.89  tff(c_15344, plain, (![C_1087, D_1088]: (r1_tarski(k2_relat_1(k2_zfmisc_1(C_1087, D_1088)), D_1088))), inference(resolution, [status(thm)], [c_15303, c_4])).
% 10.67/3.89  tff(c_7504, plain, (![A_551, C_552]: (r2_hidden(k4_tarski('#skF_5'(A_551, k2_relat_1(A_551), C_552), C_552), A_551) | ~r2_hidden(C_552, k2_relat_1(A_551)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.67/3.89  tff(c_8320, plain, (![A_642, C_643, B_644]: (r2_hidden(k4_tarski('#skF_5'(A_642, k2_relat_1(A_642), C_643), C_643), B_644) | ~r1_tarski(A_642, B_644) | ~r2_hidden(C_643, k2_relat_1(A_642)))), inference(resolution, [status(thm)], [c_7504, c_2])).
% 10.67/3.89  tff(c_11659, plain, (![A_816, C_817, C_818, D_819]: (r2_hidden('#skF_5'(A_816, k2_relat_1(A_816), C_817), C_818) | ~r1_tarski(A_816, k2_zfmisc_1(C_818, D_819)) | ~r2_hidden(C_817, k2_relat_1(A_816)))), inference(resolution, [status(thm)], [c_8320, c_12])).
% 10.67/3.89  tff(c_11750, plain, (![C_821]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_821), '#skF_7') | ~r2_hidden(C_821, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_60, c_11659])).
% 10.67/3.89  tff(c_7544, plain, (![C_556, D_557, C_558]: (r2_hidden(C_556, D_557) | ~r2_hidden(C_556, k2_relat_1(k2_zfmisc_1(C_558, D_557))))), inference(resolution, [status(thm)], [c_7504, c_10])).
% 10.67/3.89  tff(c_8096, plain, (![C_615, D_616, B_617]: (r2_hidden('#skF_1'(k2_relat_1(k2_zfmisc_1(C_615, D_616)), B_617), D_616) | r1_tarski(k2_relat_1(k2_zfmisc_1(C_615, D_616)), B_617))), inference(resolution, [status(thm)], [c_6, c_7544])).
% 10.67/3.89  tff(c_8120, plain, (![C_618, D_619]: (r1_tarski(k2_relat_1(k2_zfmisc_1(C_618, D_619)), D_619))), inference(resolution, [status(thm)], [c_8096, c_4])).
% 10.67/3.89  tff(c_7407, plain, (![A_537, B_538, C_539, D_540]: (r2_hidden(k4_tarski(A_537, B_538), k2_zfmisc_1(C_539, D_540)) | ~r2_hidden(B_538, D_540) | ~r2_hidden(A_537, C_539))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.67/3.89  tff(c_22, plain, (![C_30, A_15, D_33]: (r2_hidden(C_30, k2_relat_1(A_15)) | ~r2_hidden(k4_tarski(D_33, C_30), A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.67/3.89  tff(c_7426, plain, (![B_541, C_542, D_543, A_544]: (r2_hidden(B_541, k2_relat_1(k2_zfmisc_1(C_542, D_543))) | ~r2_hidden(B_541, D_543) | ~r2_hidden(A_544, C_542))), inference(resolution, [status(thm)], [c_7407, c_22])).
% 10.67/3.89  tff(c_7439, plain, (![B_545, D_546]: (r2_hidden(B_545, k2_relat_1(k2_zfmisc_1(k2_relat_1('#skF_8'), D_546))) | ~r2_hidden(B_545, D_546))), inference(resolution, [status(thm)], [c_7352, c_7426])).
% 10.67/3.89  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.67/3.89  tff(c_85, plain, (![A_95, C_96, B_97]: (m1_subset_1(A_95, C_96) | ~m1_subset_1(B_97, k1_zfmisc_1(C_96)) | ~r2_hidden(A_95, B_97))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.67/3.89  tff(c_90, plain, (![A_95, B_11, A_10]: (m1_subset_1(A_95, B_11) | ~r2_hidden(A_95, A_10) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_16, c_85])).
% 10.67/3.89  tff(c_7460, plain, (![B_545, B_11, D_546]: (m1_subset_1(B_545, B_11) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(k2_relat_1('#skF_8'), D_546)), B_11) | ~r2_hidden(B_545, D_546))), inference(resolution, [status(thm)], [c_7439, c_90])).
% 10.67/3.89  tff(c_8146, plain, (![B_545, D_619]: (m1_subset_1(B_545, D_619) | ~r2_hidden(B_545, D_619))), inference(resolution, [status(thm)], [c_8120, c_7460])).
% 10.67/3.89  tff(c_11767, plain, (![C_822]: (m1_subset_1('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_822), '#skF_7') | ~r2_hidden(C_822, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_11750, c_8146])).
% 10.67/3.89  tff(c_42, plain, (![E_78]: (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | ~r2_hidden(k4_tarski(E_78, '#skF_11'), '#skF_8') | ~m1_subset_1(E_78, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.67/3.89  tff(c_7363, plain, (![E_78]: (~r2_hidden(k4_tarski(E_78, '#skF_11'), '#skF_8') | ~m1_subset_1(E_78, '#skF_7'))), inference(splitLeft, [status(thm)], [c_42])).
% 10.67/3.89  tff(c_8366, plain, (![A_642]: (~m1_subset_1('#skF_5'(A_642, k2_relat_1(A_642), '#skF_11'), '#skF_7') | ~r1_tarski(A_642, '#skF_8') | ~r2_hidden('#skF_11', k2_relat_1(A_642)))), inference(resolution, [status(thm)], [c_8320, c_7363])).
% 10.67/3.89  tff(c_11771, plain, (~r1_tarski('#skF_8', '#skF_8') | ~r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_11767, c_8366])).
% 10.67/3.89  tff(c_11778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7352, c_67, c_11771])).
% 10.67/3.89  tff(c_11779, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_42])).
% 10.67/3.89  tff(c_11940, plain, (![A_842, B_843, C_844, D_845]: (r2_hidden(k4_tarski(A_842, B_843), k2_zfmisc_1(C_844, D_845)) | ~r2_hidden(B_843, D_845) | ~r2_hidden(A_842, C_844))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.67/3.89  tff(c_12249, plain, (![B_896, C_897, D_898, A_899]: (r2_hidden(B_896, k2_relat_1(k2_zfmisc_1(C_897, D_898))) | ~r2_hidden(B_896, D_898) | ~r2_hidden(A_899, C_897))), inference(resolution, [status(thm)], [c_11940, c_22])).
% 10.67/3.89  tff(c_12304, plain, (![B_900, D_901]: (r2_hidden(B_900, k2_relat_1(k2_zfmisc_1('#skF_8', D_901))) | ~r2_hidden(B_900, D_901))), inference(resolution, [status(thm)], [c_11779, c_12249])).
% 10.67/3.89  tff(c_12337, plain, (![B_900, B_11, D_901]: (m1_subset_1(B_900, B_11) | ~r1_tarski(k2_relat_1(k2_zfmisc_1('#skF_8', D_901)), B_11) | ~r2_hidden(B_900, D_901))), inference(resolution, [status(thm)], [c_12304, c_90])).
% 10.67/3.89  tff(c_15448, plain, (![B_900, D_1088]: (m1_subset_1(B_900, D_1088) | ~r2_hidden(B_900, D_1088))), inference(resolution, [status(thm)], [c_15344, c_12337])).
% 10.67/3.89  tff(c_17021, plain, (![C_1166]: (m1_subset_1('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_1166), '#skF_7') | ~r2_hidden(C_1166, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_17004, c_15448])).
% 10.67/3.89  tff(c_11789, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_11779, c_22])).
% 10.67/3.89  tff(c_40, plain, (![E_78]: (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | ~r2_hidden(k4_tarski(E_78, '#skF_11'), '#skF_8') | ~m1_subset_1(E_78, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.67/3.89  tff(c_11825, plain, (![E_78]: (~r2_hidden(k4_tarski(E_78, '#skF_11'), '#skF_8') | ~m1_subset_1(E_78, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_11789, c_7348, c_40])).
% 10.67/3.89  tff(c_12972, plain, (![A_943]: (~m1_subset_1('#skF_5'(A_943, k2_relat_1(A_943), '#skF_11'), '#skF_7') | ~r1_tarski(A_943, '#skF_8') | ~r2_hidden('#skF_11', k2_relat_1(A_943)))), inference(resolution, [status(thm)], [c_12933, c_11825])).
% 10.67/3.89  tff(c_17025, plain, (~r1_tarski('#skF_8', '#skF_8') | ~r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_17021, c_12972])).
% 10.67/3.89  tff(c_17032, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7352, c_67, c_17025])).
% 10.67/3.89  tff(c_17034, plain, (~r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_50])).
% 10.67/3.89  tff(c_48, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.67/3.89  tff(c_17055, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_17034, c_48])).
% 10.67/3.89  tff(c_17064, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_17055, c_22])).
% 10.67/3.89  tff(c_17107, plain, (![A_1191, B_1192, C_1193]: (k2_relset_1(A_1191, B_1192, C_1193)=k2_relat_1(C_1193) | ~m1_subset_1(C_1193, k1_zfmisc_1(k2_zfmisc_1(A_1191, B_1192))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.67/3.89  tff(c_17116, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_17107])).
% 10.67/3.89  tff(c_46, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.67/3.89  tff(c_17066, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_17034, c_46])).
% 10.67/3.89  tff(c_17117, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_17116, c_17066])).
% 10.67/3.89  tff(c_17121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17064, c_17117])).
% 10.67/3.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.67/3.89  
% 10.67/3.89  Inference rules
% 10.67/3.89  ----------------------
% 10.67/3.89  #Ref     : 0
% 10.67/3.89  #Sup     : 4081
% 10.67/3.89  #Fact    : 0
% 10.67/3.89  #Define  : 0
% 10.67/3.89  #Split   : 38
% 10.67/3.89  #Chain   : 0
% 10.67/3.89  #Close   : 0
% 10.67/3.89  
% 10.67/3.89  Ordering : KBO
% 10.67/3.89  
% 10.67/3.89  Simplification rules
% 10.67/3.89  ----------------------
% 10.67/3.89  #Subsume      : 614
% 10.67/3.89  #Demod        : 372
% 10.67/3.89  #Tautology    : 365
% 10.67/3.89  #SimpNegUnit  : 5
% 10.67/3.89  #BackRed      : 53
% 10.67/3.89  
% 10.67/3.89  #Partial instantiations: 0
% 10.67/3.89  #Strategies tried      : 1
% 10.67/3.89  
% 10.67/3.89  Timing (in seconds)
% 10.67/3.89  ----------------------
% 10.67/3.89  Preprocessing        : 0.32
% 10.67/3.89  Parsing              : 0.16
% 10.67/3.89  CNF conversion       : 0.03
% 10.67/3.89  Main loop            : 2.81
% 10.67/3.89  Inferencing          : 0.78
% 10.67/3.89  Reduction            : 0.77
% 10.67/3.89  Demodulation         : 0.51
% 10.67/3.89  BG Simplification    : 0.10
% 10.67/3.89  Subsumption          : 0.89
% 10.67/3.89  Abstraction          : 0.12
% 10.67/3.89  MUC search           : 0.00
% 10.67/3.89  Cooper               : 0.00
% 10.67/3.89  Total                : 3.16
% 10.67/3.89  Index Insertion      : 0.00
% 10.67/3.89  Index Deletion       : 0.00
% 10.67/3.89  Index Matching       : 0.00
% 10.67/3.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
