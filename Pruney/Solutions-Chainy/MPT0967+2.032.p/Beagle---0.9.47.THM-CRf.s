%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:17 EST 2020

% Result     : Theorem 16.52s
% Output     : CNFRefutation 16.62s
% Verified   : 
% Statistics : Number of formulae       :  303 (1366 expanded)
%              Number of leaves         :   36 ( 450 expanded)
%              Depth                    :   14
%              Number of atoms          :  542 (3764 expanded)
%              Number of equality atoms :  137 ( 987 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
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

tff(f_58,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_109,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_64,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_109,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_113,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_66,c_109])).

tff(c_53893,plain,(
    ! [C_1839,A_1840,B_1841] :
      ( r1_tarski(k2_zfmisc_1(C_1839,A_1840),k2_zfmisc_1(C_1839,B_1841))
      | ~ r1_tarski(A_1840,B_1841) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58744,plain,(
    ! [A_2057,C_2058,B_2059,A_2060] :
      ( r1_tarski(A_2057,k2_zfmisc_1(C_2058,B_2059))
      | ~ r1_tarski(A_2057,k2_zfmisc_1(C_2058,A_2060))
      | ~ r1_tarski(A_2060,B_2059) ) ),
    inference(resolution,[status(thm)],[c_53893,c_8])).

tff(c_58831,plain,(
    ! [B_2061] :
      ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_2',B_2061))
      | ~ r1_tarski('#skF_3',B_2061) ) ),
    inference(resolution,[status(thm)],[c_113,c_58744])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_104,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_60,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_72,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_60])).

tff(c_119,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_68,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_23186,plain,(
    ! [A_824,B_825,C_826] :
      ( k1_relset_1(A_824,B_825,C_826) = k1_relat_1(C_826)
      | ~ m1_subset_1(C_826,k1_zfmisc_1(k2_zfmisc_1(A_824,B_825))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_23211,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_23186])).

tff(c_23876,plain,(
    ! [B_860,A_861,C_862] :
      ( k1_xboole_0 = B_860
      | k1_relset_1(A_861,B_860,C_862) = A_861
      | ~ v1_funct_2(C_862,A_861,B_860)
      | ~ m1_subset_1(C_862,k1_zfmisc_1(k2_zfmisc_1(A_861,B_860))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_23898,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_23876])).

tff(c_23911,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_23211,c_23898])).

tff(c_23912,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_23911])).

tff(c_413,plain,(
    ! [C_85,A_86,B_87] :
      ( r1_tarski(k2_zfmisc_1(C_85,A_86),k2_zfmisc_1(C_85,B_87))
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26601,plain,(
    ! [A_970,C_971,B_972,A_973] :
      ( r1_tarski(A_970,k2_zfmisc_1(C_971,B_972))
      | ~ r1_tarski(A_970,k2_zfmisc_1(C_971,A_973))
      | ~ r1_tarski(A_973,B_972) ) ),
    inference(resolution,[status(thm)],[c_413,c_8])).

tff(c_26688,plain,(
    ! [B_974] :
      ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_2',B_974))
      | ~ r1_tarski('#skF_3',B_974) ) ),
    inference(resolution,[status(thm)],[c_113,c_26601])).

tff(c_23210,plain,(
    ! [A_824,B_825,A_17] :
      ( k1_relset_1(A_824,B_825,A_17) = k1_relat_1(A_17)
      | ~ r1_tarski(A_17,k2_zfmisc_1(A_824,B_825)) ) ),
    inference(resolution,[status(thm)],[c_30,c_23186])).

tff(c_26699,plain,(
    ! [B_974] :
      ( k1_relset_1('#skF_2',B_974,'#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_3',B_974) ) ),
    inference(resolution,[status(thm)],[c_26688,c_23210])).

tff(c_26746,plain,(
    ! [B_975] :
      ( k1_relset_1('#skF_2',B_975,'#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_3',B_975) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23912,c_26699])).

tff(c_26808,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_64,c_26746])).

tff(c_18,plain,(
    ! [C_11,A_9,B_10] :
      ( r1_tarski(k2_zfmisc_1(C_11,A_9),k2_zfmisc_1(C_11,B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_33789,plain,(
    ! [C_1141,A_1142,B_1143,B_1144] :
      ( r1_tarski(k2_zfmisc_1(C_1141,A_1142),k2_zfmisc_1(C_1141,B_1143))
      | ~ r1_tarski(B_1144,B_1143)
      | ~ r1_tarski(A_1142,B_1144) ) ),
    inference(resolution,[status(thm)],[c_18,c_26601])).

tff(c_33927,plain,(
    ! [C_1141,A_1142] :
      ( r1_tarski(k2_zfmisc_1(C_1141,A_1142),k2_zfmisc_1(C_1141,'#skF_4'))
      | ~ r1_tarski(A_1142,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_64,c_33789])).

tff(c_24,plain,(
    ! [A_14] : ~ v1_xboole_0(k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(k1_zfmisc_1(A_12),k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22894,plain,(
    ! [A_804,C_805,B_806] :
      ( m1_subset_1(A_804,C_805)
      | ~ m1_subset_1(B_806,k1_zfmisc_1(C_805))
      | ~ r2_hidden(A_804,B_806) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_23034,plain,(
    ! [A_815,B_816,A_817] :
      ( m1_subset_1(A_815,B_816)
      | ~ r2_hidden(A_815,A_817)
      | ~ r1_tarski(A_817,B_816) ) ),
    inference(resolution,[status(thm)],[c_30,c_22894])).

tff(c_29396,plain,(
    ! [A_1042,B_1043,B_1044] :
      ( m1_subset_1(A_1042,B_1043)
      | ~ r1_tarski(B_1044,B_1043)
      | v1_xboole_0(B_1044)
      | ~ m1_subset_1(A_1042,B_1044) ) ),
    inference(resolution,[status(thm)],[c_26,c_23034])).

tff(c_29458,plain,(
    ! [A_1042,B_13,A_12] :
      ( m1_subset_1(A_1042,k1_zfmisc_1(B_13))
      | v1_xboole_0(k1_zfmisc_1(A_12))
      | ~ m1_subset_1(A_1042,k1_zfmisc_1(A_12))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_22,c_29396])).

tff(c_40067,plain,(
    ! [A_1313,B_1314,A_1315] :
      ( m1_subset_1(A_1313,k1_zfmisc_1(B_1314))
      | ~ m1_subset_1(A_1313,k1_zfmisc_1(A_1315))
      | ~ r1_tarski(A_1315,B_1314) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_29458])).

tff(c_40249,plain,(
    ! [B_1322] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(B_1322))
      | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),B_1322) ) ),
    inference(resolution,[status(thm)],[c_66,c_40067])).

tff(c_40273,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_33927,c_40249])).

tff(c_40343,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_40273])).

tff(c_42,plain,(
    ! [B_26,C_27,A_25] :
      ( k1_xboole_0 = B_26
      | v1_funct_2(C_27,A_25,B_26)
      | k1_relset_1(A_25,B_26,C_27) != A_25
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40418,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_2','#skF_4')
    | k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_40343,c_42])).

tff(c_40439,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26808,c_40418])).

tff(c_40440,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_40439])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_291,plain,(
    ! [A_69,C_70,B_71] :
      ( r1_tarski(A_69,C_70)
      | ~ r1_tarski(B_71,C_70)
      | ~ r1_tarski(A_69,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24623,plain,(
    ! [A_897,B_898,A_899] :
      ( r1_tarski(A_897,k1_zfmisc_1(B_898))
      | ~ r1_tarski(A_897,k1_zfmisc_1(A_899))
      | ~ r1_tarski(A_899,B_898) ) ),
    inference(resolution,[status(thm)],[c_22,c_291])).

tff(c_29612,plain,(
    ! [A_1047,B_1048,B_1049] :
      ( r1_tarski(k1_zfmisc_1(A_1047),k1_zfmisc_1(B_1048))
      | ~ r1_tarski(B_1049,B_1048)
      | ~ r1_tarski(A_1047,B_1049) ) ),
    inference(resolution,[status(thm)],[c_22,c_24623])).

tff(c_29777,plain,(
    ! [A_1051,A_1052] :
      ( r1_tarski(k1_zfmisc_1(A_1051),k1_zfmisc_1(A_1052))
      | ~ r1_tarski(A_1051,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_29612])).

tff(c_121,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    ! [B_13,A_12] :
      ( k1_zfmisc_1(B_13) = k1_zfmisc_1(A_12)
      | ~ r1_tarski(k1_zfmisc_1(B_13),k1_zfmisc_1(A_12))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_22,c_121])).

tff(c_31629,plain,(
    ! [A_1097,A_1096] :
      ( k1_zfmisc_1(A_1097) = k1_zfmisc_1(A_1096)
      | ~ r1_tarski(A_1096,A_1097)
      | ~ r1_tarski(A_1097,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_29777,c_132])).

tff(c_31756,plain,
    ( k1_zfmisc_1('#skF_3') = k1_zfmisc_1('#skF_4')
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_64,c_31629])).

tff(c_31888,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_31756])).

tff(c_40493,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40440,c_31888])).

tff(c_40587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_40493])).

tff(c_40589,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_31756])).

tff(c_358,plain,(
    ! [A_79] :
      ( r1_tarski(A_79,k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_79,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_113,c_291])).

tff(c_478,plain,(
    ! [A_92,A_93] :
      ( r1_tarski(A_92,k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_92,A_93)
      | ~ r1_tarski(A_93,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_358,c_8])).

tff(c_517,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_478])).

tff(c_627,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_517])).

tff(c_1112,plain,(
    ! [A_131,B_132,C_133] :
      ( k1_relset_1(A_131,B_132,C_133) = k1_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1143,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1112])).

tff(c_2290,plain,(
    ! [B_201,A_202,C_203] :
      ( k1_xboole_0 = B_201
      | k1_relset_1(A_202,B_201,C_203) = A_202
      | ~ v1_funct_2(C_203,A_202,B_201)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_202,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2312,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2290])).

tff(c_2325,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1143,c_2312])).

tff(c_2326,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_2325])).

tff(c_4043,plain,(
    ! [A_274,C_275,B_276,A_277] :
      ( r1_tarski(A_274,k2_zfmisc_1(C_275,B_276))
      | ~ r1_tarski(A_274,k2_zfmisc_1(C_275,A_277))
      | ~ r1_tarski(A_277,B_276) ) ),
    inference(resolution,[status(thm)],[c_413,c_8])).

tff(c_4121,plain,(
    ! [B_278] :
      ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_2',B_278))
      | ~ r1_tarski('#skF_3',B_278) ) ),
    inference(resolution,[status(thm)],[c_113,c_4043])).

tff(c_1142,plain,(
    ! [A_131,B_132,A_17] :
      ( k1_relset_1(A_131,B_132,A_17) = k1_relat_1(A_17)
      | ~ r1_tarski(A_17,k2_zfmisc_1(A_131,B_132)) ) ),
    inference(resolution,[status(thm)],[c_30,c_1112])).

tff(c_4131,plain,(
    ! [B_278] :
      ( k1_relset_1('#skF_2',B_278,'#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_3',B_278) ) ),
    inference(resolution,[status(thm)],[c_4121,c_1142])).

tff(c_4164,plain,(
    ! [B_279] :
      ( k1_relset_1('#skF_2',B_279,'#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_3',B_279) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2326,c_4131])).

tff(c_4184,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_64,c_4164])).

tff(c_16690,plain,(
    ! [C_638,A_639,B_640,B_641] :
      ( r1_tarski(k2_zfmisc_1(C_638,A_639),k2_zfmisc_1(C_638,B_640))
      | ~ r1_tarski(B_641,B_640)
      | ~ r1_tarski(A_639,B_641) ) ),
    inference(resolution,[status(thm)],[c_18,c_4043])).

tff(c_16792,plain,(
    ! [C_638,A_639] :
      ( r1_tarski(k2_zfmisc_1(C_638,A_639),k2_zfmisc_1(C_638,'#skF_4'))
      | ~ r1_tarski(A_639,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_64,c_16690])).

tff(c_905,plain,(
    ! [A_112,C_113,B_114] :
      ( m1_subset_1(A_112,C_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(C_113))
      | ~ r2_hidden(A_112,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_925,plain,(
    ! [A_117,B_118,A_119] :
      ( m1_subset_1(A_117,B_118)
      | ~ r2_hidden(A_117,A_119)
      | ~ r1_tarski(A_119,B_118) ) ),
    inference(resolution,[status(thm)],[c_30,c_905])).

tff(c_3216,plain,(
    ! [A_249,B_250,B_251] :
      ( m1_subset_1(A_249,B_250)
      | ~ r1_tarski(B_251,B_250)
      | v1_xboole_0(B_251)
      | ~ m1_subset_1(A_249,B_251) ) ),
    inference(resolution,[status(thm)],[c_26,c_925])).

tff(c_3242,plain,(
    ! [A_249,B_13,A_12] :
      ( m1_subset_1(A_249,k1_zfmisc_1(B_13))
      | v1_xboole_0(k1_zfmisc_1(A_12))
      | ~ m1_subset_1(A_249,k1_zfmisc_1(A_12))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_22,c_3216])).

tff(c_22437,plain,(
    ! [A_797,B_798,A_799] :
      ( m1_subset_1(A_797,k1_zfmisc_1(B_798))
      | ~ m1_subset_1(A_797,k1_zfmisc_1(A_799))
      | ~ r1_tarski(A_799,B_798) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_3242])).

tff(c_22535,plain,(
    ! [B_801] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(B_801))
      | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),B_801) ) ),
    inference(resolution,[status(thm)],[c_66,c_22437])).

tff(c_22563,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_16792,c_22535])).

tff(c_22616,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_22563])).

tff(c_22642,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_2','#skF_4')
    | k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_22616,c_42])).

tff(c_22666,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4184,c_22642])).

tff(c_22667,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_22666])).

tff(c_2661,plain,(
    ! [A_221,B_222,A_223] :
      ( r1_tarski(A_221,k1_zfmisc_1(B_222))
      | ~ r1_tarski(A_221,k1_zfmisc_1(A_223))
      | ~ r1_tarski(A_223,B_222) ) ),
    inference(resolution,[status(thm)],[c_22,c_291])).

tff(c_15315,plain,(
    ! [A_602,B_603,B_604] :
      ( r1_tarski(k1_zfmisc_1(A_602),k1_zfmisc_1(B_603))
      | ~ r1_tarski(B_604,B_603)
      | ~ r1_tarski(A_602,B_604) ) ),
    inference(resolution,[status(thm)],[c_22,c_2661])).

tff(c_15446,plain,(
    ! [A_606,A_607] :
      ( r1_tarski(k1_zfmisc_1(A_606),k1_zfmisc_1(A_607))
      | ~ r1_tarski(A_606,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_15315])).

tff(c_17209,plain,(
    ! [A_653,A_652] :
      ( k1_zfmisc_1(A_653) = k1_zfmisc_1(A_652)
      | ~ r1_tarski(A_652,A_653)
      | ~ r1_tarski(A_653,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_15446,c_132])).

tff(c_17315,plain,
    ( k1_zfmisc_1('#skF_3') = k1_zfmisc_1('#skF_4')
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_64,c_17209])).

tff(c_17316,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_17315])).

tff(c_22710,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22667,c_17316])).

tff(c_22814,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_22710])).

tff(c_22816,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_17315])).

tff(c_14166,plain,(
    ! [C_580,A_581,B_582,B_583] :
      ( r1_tarski(k2_zfmisc_1(C_580,A_581),k2_zfmisc_1(C_580,B_582))
      | ~ r1_tarski(B_583,B_582)
      | ~ r1_tarski(A_581,B_583) ) ),
    inference(resolution,[status(thm)],[c_18,c_4043])).

tff(c_14349,plain,(
    ! [C_592,A_593] :
      ( r1_tarski(k2_zfmisc_1(C_592,A_593),k2_zfmisc_1(C_592,'#skF_4'))
      | ~ r1_tarski(A_593,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_64,c_14166])).

tff(c_13413,plain,(
    ! [A_555,B_556,A_557] :
      ( m1_subset_1(A_555,k1_zfmisc_1(B_556))
      | ~ m1_subset_1(A_555,k1_zfmisc_1(A_557))
      | ~ r1_tarski(A_557,B_556) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_3242])).

tff(c_13445,plain,(
    ! [B_556] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(B_556))
      | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),B_556) ) ),
    inference(resolution,[status(thm)],[c_66,c_13413])).

tff(c_14357,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_14349,c_13445])).

tff(c_14461,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14357])).

tff(c_14504,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_2','#skF_4')
    | k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_14461,c_42])).

tff(c_14527,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4184,c_14504])).

tff(c_14528,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_14527])).

tff(c_7876,plain,(
    ! [A_385,B_386,B_387] :
      ( r1_tarski(k1_zfmisc_1(A_385),k1_zfmisc_1(B_386))
      | ~ r1_tarski(B_387,B_386)
      | ~ r1_tarski(A_385,B_387) ) ),
    inference(resolution,[status(thm)],[c_22,c_2661])).

tff(c_7946,plain,(
    ! [A_388,A_389] :
      ( r1_tarski(k1_zfmisc_1(A_388),k1_zfmisc_1(A_389))
      | ~ r1_tarski(A_388,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_7876])).

tff(c_8126,plain,(
    ! [A_396,A_395] :
      ( k1_zfmisc_1(A_396) = k1_zfmisc_1(A_395)
      | ~ r1_tarski(A_395,A_396)
      | ~ r1_tarski(A_396,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_7946,c_132])).

tff(c_8205,plain,
    ( k1_zfmisc_1('#skF_3') = k1_zfmisc_1('#skF_4')
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_64,c_8126])).

tff(c_8206,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_8205])).

tff(c_14578,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14528,c_8206])).

tff(c_14674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14578])).

tff(c_14676,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_8205])).

tff(c_4114,plain,(
    ! [B_276] :
      ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_2',B_276))
      | ~ r1_tarski('#skF_3',B_276) ) ),
    inference(resolution,[status(thm)],[c_113,c_4043])).

tff(c_14,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_450,plain,(
    ! [A_90,A_91] :
      ( r1_tarski(k2_zfmisc_1(A_90,A_91),k1_xboole_0)
      | ~ r1_tarski(A_91,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_413])).

tff(c_7547,plain,(
    ! [A_373,A_374,A_375] :
      ( r1_tarski(A_373,k1_xboole_0)
      | ~ r1_tarski(A_373,k2_zfmisc_1(A_374,A_375))
      | ~ r1_tarski(A_375,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_450,c_8])).

tff(c_7655,plain,(
    ! [B_276] :
      ( r1_tarski('#skF_5',k1_xboole_0)
      | ~ r1_tarski(B_276,k1_xboole_0)
      | ~ r1_tarski('#skF_3',B_276) ) ),
    inference(resolution,[status(thm)],[c_4114,c_7547])).

tff(c_7675,plain,(
    ! [B_276] :
      ( ~ r1_tarski(B_276,k1_xboole_0)
      | ~ r1_tarski('#skF_3',B_276) ) ),
    inference(splitLeft,[status(thm)],[c_7655])).

tff(c_14684,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_14676,c_7675])).

tff(c_14727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_14684])).

tff(c_14728,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_7655])).

tff(c_134,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_121])).

tff(c_14781,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_14728,c_134])).

tff(c_16,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_155,plain,(
    ! [A_57,B_58] : m1_subset_1('#skF_1'(A_57,B_58),k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_166,plain,(
    ! [B_59] : m1_subset_1('#skF_1'(k1_xboole_0,B_59),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_155])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_172,plain,(
    ! [B_60] : r1_tarski('#skF_1'(k1_xboole_0,B_60),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_166,c_28])).

tff(c_178,plain,(
    ! [B_60] : '#skF_1'(k1_xboole_0,B_60) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_172,c_134])).

tff(c_161,plain,(
    ! [B_8] : m1_subset_1('#skF_1'(k1_xboole_0,B_8),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_155])).

tff(c_183,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_161])).

tff(c_58,plain,(
    ! [A_28,B_29] : m1_subset_1('#skF_1'(A_28,B_29),k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1148,plain,(
    ! [A_134,B_135] : k1_relset_1(A_134,B_135,'#skF_1'(A_134,B_135)) = k1_relat_1('#skF_1'(A_134,B_135)) ),
    inference(resolution,[status(thm)],[c_58,c_1112])).

tff(c_1160,plain,(
    ! [B_60] : k1_relat_1('#skF_1'(k1_xboole_0,B_60)) = k1_relset_1(k1_xboole_0,B_60,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_1148])).

tff(c_1164,plain,(
    ! [B_60] : k1_relset_1(k1_xboole_0,B_60,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_1160])).

tff(c_48,plain,(
    ! [A_28,B_29] : v1_funct_2('#skF_1'(A_28,B_29),A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_44,plain,(
    ! [B_26,C_27] :
      ( k1_relset_1(k1_xboole_0,B_26,C_27) = k1_xboole_0
      | ~ v1_funct_2(C_27,k1_xboole_0,B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1625,plain,(
    ! [B_166,C_167] :
      ( k1_relset_1(k1_xboole_0,B_166,C_167) = k1_xboole_0
      | ~ v1_funct_2(C_167,k1_xboole_0,B_166)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_44])).

tff(c_1633,plain,(
    ! [B_29] :
      ( k1_relset_1(k1_xboole_0,B_29,'#skF_1'(k1_xboole_0,B_29)) = k1_xboole_0
      | ~ m1_subset_1('#skF_1'(k1_xboole_0,B_29),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_48,c_1625])).

tff(c_1642,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_178,c_1164,c_178,c_1633])).

tff(c_14842,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14781,c_14781,c_1642])).

tff(c_14881,plain,(
    '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2326,c_14842])).

tff(c_303,plain,(
    ! [A_69] :
      ( r1_tarski(A_69,k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_69,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_113,c_291])).

tff(c_365,plain,(
    ! [A_80,C_81,B_82] :
      ( r1_tarski(k2_zfmisc_1(A_80,C_81),k2_zfmisc_1(B_82,C_81))
      | ~ r1_tarski(A_80,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4429,plain,(
    ! [A_289,B_290,C_291,A_292] :
      ( r1_tarski(A_289,k2_zfmisc_1(B_290,C_291))
      | ~ r1_tarski(A_289,k2_zfmisc_1(A_292,C_291))
      | ~ r1_tarski(A_292,B_290) ) ),
    inference(resolution,[status(thm)],[c_365,c_8])).

tff(c_4513,plain,(
    ! [B_293] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(B_293,'#skF_3'))
      | ~ r1_tarski('#skF_2',B_293) ) ),
    inference(resolution,[status(thm)],[c_113,c_4429])).

tff(c_4525,plain,(
    ! [B_293] :
      ( k1_relset_1(B_293,'#skF_3','#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',B_293) ) ),
    inference(resolution,[status(thm)],[c_4513,c_1142])).

tff(c_4710,plain,(
    ! [B_299] :
      ( k1_relset_1(B_299,'#skF_3','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',B_299) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2326,c_4525])).

tff(c_4724,plain,
    ( k1_relset_1(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_3','#skF_5') = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_5') ),
    inference(resolution,[status(thm)],[c_303,c_4710])).

tff(c_7546,plain,(
    ~ r1_tarski('#skF_2','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4724])).

tff(c_14962,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14881,c_7546])).

tff(c_14997,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14962])).

tff(c_14999,plain,(
    r1_tarski('#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_4724])).

tff(c_15218,plain,(
    ! [A_601] :
      ( r1_tarski(A_601,'#skF_5')
      | ~ r1_tarski(A_601,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14999,c_8])).

tff(c_15292,plain,(
    ! [A_3,A_601] :
      ( r1_tarski(A_3,'#skF_5')
      | ~ r1_tarski(A_3,A_601)
      | ~ r1_tarski(A_601,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_15218,c_8])).

tff(c_22826,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_22816,c_15292])).

tff(c_22878,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_22826])).

tff(c_22880,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_627,c_22878])).

tff(c_22881,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_517])).

tff(c_26674,plain,(
    ! [B_972] :
      ( r1_tarski('#skF_3',k2_zfmisc_1('#skF_2',B_972))
      | ~ r1_tarski('#skF_3',B_972) ) ),
    inference(resolution,[status(thm)],[c_22881,c_26601])).

tff(c_304,plain,(
    ! [A_69,A_6] :
      ( r1_tarski(A_69,A_6)
      | ~ r1_tarski(A_69,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_291])).

tff(c_580,plain,(
    ! [A_99,A_100,A_101] :
      ( r1_tarski(k2_zfmisc_1(A_99,A_100),A_101)
      | ~ r1_tarski(A_100,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_450,c_304])).

tff(c_133,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_113,c_121])).

tff(c_171,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_619,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_580,c_171])).

tff(c_471,plain,(
    ! [A_90,A_91] :
      ( k2_zfmisc_1(A_90,A_91) = k1_xboole_0
      | ~ r1_tarski(A_91,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_450,c_134])).

tff(c_613,plain,(
    ! [A_90,A_99,A_100] :
      ( k2_zfmisc_1(A_90,k2_zfmisc_1(A_99,A_100)) = k1_xboole_0
      | ~ r1_tarski(A_100,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_580,c_471])).

tff(c_26987,plain,(
    ! [B_982] :
      ( r1_tarski('#skF_3',k2_zfmisc_1('#skF_2',B_982))
      | ~ r1_tarski('#skF_3',B_982) ) ),
    inference(resolution,[status(thm)],[c_22881,c_26601])).

tff(c_27022,plain,(
    ! [A_99,A_100] :
      ( r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski('#skF_3',k2_zfmisc_1(A_99,A_100))
      | ~ r1_tarski(A_100,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_26987])).

tff(c_27242,plain,(
    ! [A_989,A_990] :
      ( ~ r1_tarski('#skF_3',k2_zfmisc_1(A_989,A_990))
      | ~ r1_tarski(A_990,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_619,c_27022])).

tff(c_27286,plain,(
    ! [B_972] :
      ( ~ r1_tarski(B_972,k1_xboole_0)
      | ~ r1_tarski('#skF_3',B_972) ) ),
    inference(resolution,[status(thm)],[c_26674,c_27242])).

tff(c_40605,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40589,c_27286])).

tff(c_40659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_40605])).

tff(c_40660,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_40677,plain,(
    ! [B_1324,A_1325] :
      ( k1_xboole_0 = B_1324
      | k1_xboole_0 = A_1325
      | k2_zfmisc_1(A_1325,B_1324) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_40680,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_40660,c_40677])).

tff(c_40687,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_40680])).

tff(c_40692,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_40687])).

tff(c_40663,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40660,c_66])).

tff(c_41677,plain,(
    ! [A_1391,B_1392,C_1393] :
      ( k1_relset_1(A_1391,B_1392,C_1393) = k1_relat_1(C_1393)
      | ~ m1_subset_1(C_1393,k1_zfmisc_1(k2_zfmisc_1(A_1391,B_1392))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_41709,plain,(
    ! [C_1394] :
      ( k1_relset_1('#skF_2','#skF_3',C_1394) = k1_relat_1(C_1394)
      | ~ m1_subset_1(C_1394,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40660,c_41677])).

tff(c_41721,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40663,c_41709])).

tff(c_42971,plain,(
    ! [B_1468,A_1469,C_1470] :
      ( k1_xboole_0 = B_1468
      | k1_relset_1(A_1469,B_1468,C_1470) = A_1469
      | ~ v1_funct_2(C_1470,A_1469,B_1468)
      | ~ m1_subset_1(C_1470,k1_zfmisc_1(k2_zfmisc_1(A_1469,B_1468))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_42986,plain,(
    ! [C_1470] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_1470) = '#skF_2'
      | ~ v1_funct_2(C_1470,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_1470,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40660,c_42971])).

tff(c_43177,plain,(
    ! [C_1480] :
      ( k1_relset_1('#skF_2','#skF_3',C_1480) = '#skF_2'
      | ~ v1_funct_2(C_1480,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_1480,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_42986])).

tff(c_43183,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40663,c_43177])).

tff(c_43193,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_41721,c_43183])).

tff(c_40833,plain,(
    ! [C_1338,A_1339,B_1340] :
      ( r1_tarski(k2_zfmisc_1(C_1338,A_1339),k2_zfmisc_1(C_1338,B_1340))
      | ~ r1_tarski(A_1339,B_1340) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_40840,plain,(
    ! [B_1340] :
      ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_2',B_1340))
      | ~ r1_tarski('#skF_3',B_1340) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40660,c_40833])).

tff(c_43418,plain,(
    ! [A_1489,B_1490,A_1491] :
      ( k1_relset_1(A_1489,B_1490,A_1491) = k1_relat_1(A_1491)
      | ~ r1_tarski(A_1491,k2_zfmisc_1(A_1489,B_1490)) ) ),
    inference(resolution,[status(thm)],[c_30,c_41677])).

tff(c_43462,plain,(
    ! [B_1340] :
      ( k1_relset_1('#skF_2',B_1340,'#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_3',B_1340) ) ),
    inference(resolution,[status(thm)],[c_40840,c_43418])).

tff(c_43525,plain,(
    ! [B_1495] :
      ( k1_relset_1('#skF_2',B_1495,'#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_3',B_1495) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43193,c_43462])).

tff(c_43540,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_64,c_43525])).

tff(c_45991,plain,(
    ! [A_1579,C_1580,B_1581,A_1582] :
      ( r1_tarski(A_1579,k2_zfmisc_1(C_1580,B_1581))
      | ~ r1_tarski(A_1579,k2_zfmisc_1(C_1580,A_1582))
      | ~ r1_tarski(A_1582,B_1581) ) ),
    inference(resolution,[status(thm)],[c_40833,c_8])).

tff(c_52964,plain,(
    ! [C_1784,A_1785,B_1786,B_1787] :
      ( r1_tarski(k2_zfmisc_1(C_1784,A_1785),k2_zfmisc_1(C_1784,B_1786))
      | ~ r1_tarski(B_1787,B_1786)
      | ~ r1_tarski(A_1785,B_1787) ) ),
    inference(resolution,[status(thm)],[c_18,c_45991])).

tff(c_53071,plain,(
    ! [C_1788,A_1789] :
      ( r1_tarski(k2_zfmisc_1(C_1788,A_1789),k2_zfmisc_1(C_1788,'#skF_4'))
      | ~ r1_tarski(A_1789,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_64,c_52964])).

tff(c_53162,plain,
    ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40660,c_53071])).

tff(c_53203,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_53162])).

tff(c_42476,plain,(
    ! [B_1446,C_1447,A_1448] :
      ( k1_xboole_0 = B_1446
      | v1_funct_2(C_1447,A_1448,B_1446)
      | k1_relset_1(A_1448,B_1446,C_1447) != A_1448
      | ~ m1_subset_1(C_1447,k1_zfmisc_1(k2_zfmisc_1(A_1448,B_1446))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_42508,plain,(
    ! [B_1446,A_17,A_1448] :
      ( k1_xboole_0 = B_1446
      | v1_funct_2(A_17,A_1448,B_1446)
      | k1_relset_1(A_1448,B_1446,A_17) != A_1448
      | ~ r1_tarski(A_17,k2_zfmisc_1(A_1448,B_1446)) ) ),
    inference(resolution,[status(thm)],[c_30,c_42476])).

tff(c_53228,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_2','#skF_4')
    | k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_53203,c_42508])).

tff(c_53260,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43540,c_53228])).

tff(c_53261,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_53260])).

tff(c_40732,plain,(
    ! [A_1329,C_1330,B_1331] :
      ( r1_tarski(A_1329,C_1330)
      | ~ r1_tarski(B_1331,C_1330)
      | ~ r1_tarski(A_1329,B_1331) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_43858,plain,(
    ! [A_1510,B_1511,A_1512] :
      ( r1_tarski(A_1510,k1_zfmisc_1(B_1511))
      | ~ r1_tarski(A_1510,k1_zfmisc_1(A_1512))
      | ~ r1_tarski(A_1512,B_1511) ) ),
    inference(resolution,[status(thm)],[c_22,c_40732])).

tff(c_50092,plain,(
    ! [A_1690,B_1691,B_1692] :
      ( r1_tarski(k1_zfmisc_1(A_1690),k1_zfmisc_1(B_1691))
      | ~ r1_tarski(B_1692,B_1691)
      | ~ r1_tarski(A_1690,B_1692) ) ),
    inference(resolution,[status(thm)],[c_22,c_43858])).

tff(c_50186,plain,(
    ! [A_1693,A_1694] :
      ( r1_tarski(k1_zfmisc_1(A_1693),k1_zfmisc_1(A_1694))
      | ~ r1_tarski(A_1693,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_50092])).

tff(c_50258,plain,(
    ! [A_1697,A_1696] :
      ( k1_zfmisc_1(A_1697) = k1_zfmisc_1(A_1696)
      | ~ r1_tarski(A_1696,A_1697)
      | ~ r1_tarski(A_1697,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_50186,c_132])).

tff(c_50362,plain,
    ( k1_zfmisc_1('#skF_3') = k1_zfmisc_1('#skF_4')
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_64,c_50258])).

tff(c_50363,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_50362])).

tff(c_53300,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53261,c_50363])).

tff(c_53408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_53300])).

tff(c_53410,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_50362])).

tff(c_40912,plain,(
    ! [A_1346,A_1347] :
      ( r1_tarski(k2_zfmisc_1(A_1346,A_1347),k1_xboole_0)
      | ~ r1_tarski(A_1347,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_40833])).

tff(c_44001,plain,(
    ! [A_1517,A_1518,A_1519] :
      ( r1_tarski(A_1517,k1_xboole_0)
      | ~ r1_tarski(A_1517,k2_zfmisc_1(A_1518,A_1519))
      | ~ r1_tarski(A_1519,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40912,c_8])).

tff(c_44082,plain,(
    ! [B_1340] :
      ( r1_tarski('#skF_5',k1_xboole_0)
      | ~ r1_tarski(B_1340,k1_xboole_0)
      | ~ r1_tarski('#skF_3',B_1340) ) ),
    inference(resolution,[status(thm)],[c_40840,c_44001])).

tff(c_44732,plain,(
    ! [B_1340] :
      ( ~ r1_tarski(B_1340,k1_xboole_0)
      | ~ r1_tarski('#skF_3',B_1340) ) ),
    inference(splitLeft,[status(thm)],[c_44082])).

tff(c_53423,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_53410,c_44732])).

tff(c_53455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_53423])).

tff(c_53456,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_44082])).

tff(c_53473,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_53456,c_134])).

tff(c_53488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40692,c_53473])).

tff(c_53489,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_40687])).

tff(c_53497,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53489,c_10])).

tff(c_170,plain,(
    ! [B_59] : r1_tarski('#skF_1'(k1_xboole_0,B_59),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_166,c_28])).

tff(c_53574,plain,(
    ! [B_1797] : r1_tarski('#skF_1'('#skF_2',B_1797),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53489,c_53489,c_170])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53578,plain,(
    ! [B_1797] :
      ( '#skF_1'('#skF_2',B_1797) = '#skF_2'
      | ~ r1_tarski('#skF_2','#skF_1'('#skF_2',B_1797)) ) ),
    inference(resolution,[status(thm)],[c_53574,c_2])).

tff(c_53585,plain,(
    ! [B_1798] : '#skF_1'('#skF_2',B_1798) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53497,c_53578])).

tff(c_53593,plain,(
    ! [B_1798] : v1_funct_2('#skF_2','#skF_2',B_1798) ),
    inference(superposition,[status(thm),theory(equality)],[c_53585,c_48])).

tff(c_53490,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_40687])).

tff(c_53512,plain,(
    '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53489,c_53490])).

tff(c_53515,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53512,c_119])).

tff(c_53627,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53593,c_53515])).

tff(c_53628,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_53633,plain,(
    ~ r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_53628])).

tff(c_58852,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58831,c_53633])).

tff(c_58882,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58852])).

tff(c_58884,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_58883,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_58892,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58884,c_58883])).

tff(c_58885,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_2',B_8) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58883,c_58883,c_16])).

tff(c_58915,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_3',B_8) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58892,c_58892,c_58885])).

tff(c_59007,plain,(
    ! [A_2086,B_2087] : m1_subset_1('#skF_1'(A_2086,B_2087),k1_zfmisc_1(k2_zfmisc_1(A_2086,B_2087))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_59028,plain,(
    ! [B_2091] : m1_subset_1('#skF_1'('#skF_3',B_2091),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58915,c_59007])).

tff(c_59033,plain,(
    ! [B_2092] : r1_tarski('#skF_1'('#skF_3',B_2092),'#skF_3') ),
    inference(resolution,[status(thm)],[c_59028,c_28])).

tff(c_58887,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58883,c_10])).

tff(c_58903,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58892,c_58887])).

tff(c_58947,plain,(
    ! [B_2077,A_2078] :
      ( B_2077 = A_2078
      | ~ r1_tarski(B_2077,A_2078)
      | ~ r1_tarski(A_2078,B_2077) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58957,plain,(
    ! [A_6] :
      ( A_6 = '#skF_3'
      | ~ r1_tarski(A_6,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_58903,c_58947])).

tff(c_59050,plain,(
    ! [B_2093] : '#skF_1'('#skF_3',B_2093) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_59033,c_58957])).

tff(c_59058,plain,(
    ! [B_2093] : v1_funct_2('#skF_3','#skF_3',B_2093) ),
    inference(superposition,[status(thm),theory(equality)],[c_59050,c_48])).

tff(c_58886,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58883,c_58883,c_14])).

tff(c_58906,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58892,c_58892,c_58886])).

tff(c_58897,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58892,c_66])).

tff(c_58933,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58906,c_58897])).

tff(c_58937,plain,(
    ! [A_2073,B_2074] :
      ( r1_tarski(A_2073,B_2074)
      | ~ m1_subset_1(A_2073,k1_zfmisc_1(B_2074)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_58941,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_58933,c_58937])).

tff(c_58949,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_58941,c_58947])).

tff(c_58956,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58903,c_58949])).

tff(c_58935,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58892,c_58933,c_58915,c_58892,c_72])).

tff(c_58975,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58956,c_58935])).

tff(c_59103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59058,c_58975])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:59:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.52/7.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.62/7.85  
% 16.62/7.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.62/7.85  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 16.62/7.85  
% 16.62/7.85  %Foreground sorts:
% 16.62/7.85  
% 16.62/7.85  
% 16.62/7.85  %Background operators:
% 16.62/7.85  
% 16.62/7.85  
% 16.62/7.85  %Foreground operators:
% 16.62/7.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.62/7.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.62/7.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.62/7.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.62/7.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.62/7.85  tff('#skF_5', type, '#skF_5': $i).
% 16.62/7.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 16.62/7.85  tff('#skF_2', type, '#skF_2': $i).
% 16.62/7.85  tff('#skF_3', type, '#skF_3': $i).
% 16.62/7.85  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 16.62/7.85  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 16.62/7.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.62/7.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.62/7.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.62/7.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.62/7.85  tff('#skF_4', type, '#skF_4': $i).
% 16.62/7.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.62/7.85  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 16.62/7.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.62/7.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.62/7.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.62/7.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.62/7.85  
% 16.62/7.89  tff(f_129, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 16.62/7.89  tff(f_68, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 16.62/7.89  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 16.62/7.89  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 16.62/7.89  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.62/7.89  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 16.62/7.89  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 16.62/7.89  tff(f_58, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 16.62/7.89  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 16.62/7.89  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 16.62/7.89  tff(f_74, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 16.62/7.89  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 16.62/7.89  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 16.62/7.89  tff(f_109, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 16.62/7.89  tff(c_64, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 16.62/7.89  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 16.62/7.89  tff(c_109, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.62/7.89  tff(c_113, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_66, c_109])).
% 16.62/7.89  tff(c_53893, plain, (![C_1839, A_1840, B_1841]: (r1_tarski(k2_zfmisc_1(C_1839, A_1840), k2_zfmisc_1(C_1839, B_1841)) | ~r1_tarski(A_1840, B_1841))), inference(cnfTransformation, [status(thm)], [f_51])).
% 16.62/7.89  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.62/7.89  tff(c_58744, plain, (![A_2057, C_2058, B_2059, A_2060]: (r1_tarski(A_2057, k2_zfmisc_1(C_2058, B_2059)) | ~r1_tarski(A_2057, k2_zfmisc_1(C_2058, A_2060)) | ~r1_tarski(A_2060, B_2059))), inference(resolution, [status(thm)], [c_53893, c_8])).
% 16.62/7.89  tff(c_58831, plain, (![B_2061]: (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', B_2061)) | ~r1_tarski('#skF_3', B_2061))), inference(resolution, [status(thm)], [c_113, c_58744])).
% 16.62/7.89  tff(c_30, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.62/7.89  tff(c_62, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_129])).
% 16.62/7.89  tff(c_104, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_62])).
% 16.62/7.89  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.62/7.89  tff(c_70, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 16.62/7.89  tff(c_60, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 16.62/7.89  tff(c_72, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_60])).
% 16.62/7.89  tff(c_119, plain, (~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_72])).
% 16.62/7.89  tff(c_68, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 16.62/7.89  tff(c_23186, plain, (![A_824, B_825, C_826]: (k1_relset_1(A_824, B_825, C_826)=k1_relat_1(C_826) | ~m1_subset_1(C_826, k1_zfmisc_1(k2_zfmisc_1(A_824, B_825))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 16.62/7.89  tff(c_23211, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_23186])).
% 16.62/7.89  tff(c_23876, plain, (![B_860, A_861, C_862]: (k1_xboole_0=B_860 | k1_relset_1(A_861, B_860, C_862)=A_861 | ~v1_funct_2(C_862, A_861, B_860) | ~m1_subset_1(C_862, k1_zfmisc_1(k2_zfmisc_1(A_861, B_860))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 16.62/7.89  tff(c_23898, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_23876])).
% 16.62/7.89  tff(c_23911, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_23211, c_23898])).
% 16.62/7.89  tff(c_23912, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_104, c_23911])).
% 16.62/7.89  tff(c_413, plain, (![C_85, A_86, B_87]: (r1_tarski(k2_zfmisc_1(C_85, A_86), k2_zfmisc_1(C_85, B_87)) | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_51])).
% 16.62/7.89  tff(c_26601, plain, (![A_970, C_971, B_972, A_973]: (r1_tarski(A_970, k2_zfmisc_1(C_971, B_972)) | ~r1_tarski(A_970, k2_zfmisc_1(C_971, A_973)) | ~r1_tarski(A_973, B_972))), inference(resolution, [status(thm)], [c_413, c_8])).
% 16.62/7.89  tff(c_26688, plain, (![B_974]: (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', B_974)) | ~r1_tarski('#skF_3', B_974))), inference(resolution, [status(thm)], [c_113, c_26601])).
% 16.62/7.89  tff(c_23210, plain, (![A_824, B_825, A_17]: (k1_relset_1(A_824, B_825, A_17)=k1_relat_1(A_17) | ~r1_tarski(A_17, k2_zfmisc_1(A_824, B_825)))), inference(resolution, [status(thm)], [c_30, c_23186])).
% 16.62/7.89  tff(c_26699, plain, (![B_974]: (k1_relset_1('#skF_2', B_974, '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_3', B_974))), inference(resolution, [status(thm)], [c_26688, c_23210])).
% 16.62/7.89  tff(c_26746, plain, (![B_975]: (k1_relset_1('#skF_2', B_975, '#skF_5')='#skF_2' | ~r1_tarski('#skF_3', B_975))), inference(demodulation, [status(thm), theory('equality')], [c_23912, c_26699])).
% 16.62/7.89  tff(c_26808, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_64, c_26746])).
% 16.62/7.89  tff(c_18, plain, (![C_11, A_9, B_10]: (r1_tarski(k2_zfmisc_1(C_11, A_9), k2_zfmisc_1(C_11, B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 16.62/7.89  tff(c_33789, plain, (![C_1141, A_1142, B_1143, B_1144]: (r1_tarski(k2_zfmisc_1(C_1141, A_1142), k2_zfmisc_1(C_1141, B_1143)) | ~r1_tarski(B_1144, B_1143) | ~r1_tarski(A_1142, B_1144))), inference(resolution, [status(thm)], [c_18, c_26601])).
% 16.62/7.89  tff(c_33927, plain, (![C_1141, A_1142]: (r1_tarski(k2_zfmisc_1(C_1141, A_1142), k2_zfmisc_1(C_1141, '#skF_4')) | ~r1_tarski(A_1142, '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_33789])).
% 16.62/7.89  tff(c_24, plain, (![A_14]: (~v1_xboole_0(k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 16.62/7.89  tff(c_22, plain, (![A_12, B_13]: (r1_tarski(k1_zfmisc_1(A_12), k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 16.62/7.89  tff(c_26, plain, (![A_15, B_16]: (r2_hidden(A_15, B_16) | v1_xboole_0(B_16) | ~m1_subset_1(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 16.62/7.89  tff(c_22894, plain, (![A_804, C_805, B_806]: (m1_subset_1(A_804, C_805) | ~m1_subset_1(B_806, k1_zfmisc_1(C_805)) | ~r2_hidden(A_804, B_806))), inference(cnfTransformation, [status(thm)], [f_74])).
% 16.62/7.89  tff(c_23034, plain, (![A_815, B_816, A_817]: (m1_subset_1(A_815, B_816) | ~r2_hidden(A_815, A_817) | ~r1_tarski(A_817, B_816))), inference(resolution, [status(thm)], [c_30, c_22894])).
% 16.62/7.89  tff(c_29396, plain, (![A_1042, B_1043, B_1044]: (m1_subset_1(A_1042, B_1043) | ~r1_tarski(B_1044, B_1043) | v1_xboole_0(B_1044) | ~m1_subset_1(A_1042, B_1044))), inference(resolution, [status(thm)], [c_26, c_23034])).
% 16.62/7.89  tff(c_29458, plain, (![A_1042, B_13, A_12]: (m1_subset_1(A_1042, k1_zfmisc_1(B_13)) | v1_xboole_0(k1_zfmisc_1(A_12)) | ~m1_subset_1(A_1042, k1_zfmisc_1(A_12)) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_22, c_29396])).
% 16.62/7.89  tff(c_40067, plain, (![A_1313, B_1314, A_1315]: (m1_subset_1(A_1313, k1_zfmisc_1(B_1314)) | ~m1_subset_1(A_1313, k1_zfmisc_1(A_1315)) | ~r1_tarski(A_1315, B_1314))), inference(negUnitSimplification, [status(thm)], [c_24, c_29458])).
% 16.62/7.89  tff(c_40249, plain, (![B_1322]: (m1_subset_1('#skF_5', k1_zfmisc_1(B_1322)) | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), B_1322))), inference(resolution, [status(thm)], [c_66, c_40067])).
% 16.62/7.89  tff(c_40273, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_33927, c_40249])).
% 16.62/7.89  tff(c_40343, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_40273])).
% 16.62/7.89  tff(c_42, plain, (![B_26, C_27, A_25]: (k1_xboole_0=B_26 | v1_funct_2(C_27, A_25, B_26) | k1_relset_1(A_25, B_26, C_27)!=A_25 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 16.62/7.89  tff(c_40418, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_2', '#skF_4') | k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2'), inference(resolution, [status(thm)], [c_40343, c_42])).
% 16.62/7.89  tff(c_40439, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26808, c_40418])).
% 16.62/7.89  tff(c_40440, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_119, c_40439])).
% 16.62/7.89  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.62/7.89  tff(c_291, plain, (![A_69, C_70, B_71]: (r1_tarski(A_69, C_70) | ~r1_tarski(B_71, C_70) | ~r1_tarski(A_69, B_71))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.62/7.89  tff(c_24623, plain, (![A_897, B_898, A_899]: (r1_tarski(A_897, k1_zfmisc_1(B_898)) | ~r1_tarski(A_897, k1_zfmisc_1(A_899)) | ~r1_tarski(A_899, B_898))), inference(resolution, [status(thm)], [c_22, c_291])).
% 16.62/7.89  tff(c_29612, plain, (![A_1047, B_1048, B_1049]: (r1_tarski(k1_zfmisc_1(A_1047), k1_zfmisc_1(B_1048)) | ~r1_tarski(B_1049, B_1048) | ~r1_tarski(A_1047, B_1049))), inference(resolution, [status(thm)], [c_22, c_24623])).
% 16.62/7.89  tff(c_29777, plain, (![A_1051, A_1052]: (r1_tarski(k1_zfmisc_1(A_1051), k1_zfmisc_1(A_1052)) | ~r1_tarski(A_1051, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_29612])).
% 16.62/7.89  tff(c_121, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.62/7.89  tff(c_132, plain, (![B_13, A_12]: (k1_zfmisc_1(B_13)=k1_zfmisc_1(A_12) | ~r1_tarski(k1_zfmisc_1(B_13), k1_zfmisc_1(A_12)) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_22, c_121])).
% 16.62/7.89  tff(c_31629, plain, (![A_1097, A_1096]: (k1_zfmisc_1(A_1097)=k1_zfmisc_1(A_1096) | ~r1_tarski(A_1096, A_1097) | ~r1_tarski(A_1097, k1_xboole_0))), inference(resolution, [status(thm)], [c_29777, c_132])).
% 16.62/7.89  tff(c_31756, plain, (k1_zfmisc_1('#skF_3')=k1_zfmisc_1('#skF_4') | ~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_31629])).
% 16.62/7.89  tff(c_31888, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_31756])).
% 16.62/7.89  tff(c_40493, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40440, c_31888])).
% 16.62/7.89  tff(c_40587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_40493])).
% 16.62/7.89  tff(c_40589, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_31756])).
% 16.62/7.89  tff(c_358, plain, (![A_79]: (r1_tarski(A_79, k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski(A_79, '#skF_5'))), inference(resolution, [status(thm)], [c_113, c_291])).
% 16.62/7.89  tff(c_478, plain, (![A_92, A_93]: (r1_tarski(A_92, k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski(A_92, A_93) | ~r1_tarski(A_93, '#skF_5'))), inference(resolution, [status(thm)], [c_358, c_8])).
% 16.62/7.89  tff(c_517, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_478])).
% 16.62/7.89  tff(c_627, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_517])).
% 16.62/7.89  tff(c_1112, plain, (![A_131, B_132, C_133]: (k1_relset_1(A_131, B_132, C_133)=k1_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 16.62/7.89  tff(c_1143, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_1112])).
% 16.62/7.89  tff(c_2290, plain, (![B_201, A_202, C_203]: (k1_xboole_0=B_201 | k1_relset_1(A_202, B_201, C_203)=A_202 | ~v1_funct_2(C_203, A_202, B_201) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_202, B_201))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 16.62/7.89  tff(c_2312, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_2290])).
% 16.62/7.89  tff(c_2325, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1143, c_2312])).
% 16.62/7.89  tff(c_2326, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_104, c_2325])).
% 16.62/7.89  tff(c_4043, plain, (![A_274, C_275, B_276, A_277]: (r1_tarski(A_274, k2_zfmisc_1(C_275, B_276)) | ~r1_tarski(A_274, k2_zfmisc_1(C_275, A_277)) | ~r1_tarski(A_277, B_276))), inference(resolution, [status(thm)], [c_413, c_8])).
% 16.62/7.89  tff(c_4121, plain, (![B_278]: (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', B_278)) | ~r1_tarski('#skF_3', B_278))), inference(resolution, [status(thm)], [c_113, c_4043])).
% 16.62/7.89  tff(c_1142, plain, (![A_131, B_132, A_17]: (k1_relset_1(A_131, B_132, A_17)=k1_relat_1(A_17) | ~r1_tarski(A_17, k2_zfmisc_1(A_131, B_132)))), inference(resolution, [status(thm)], [c_30, c_1112])).
% 16.62/7.89  tff(c_4131, plain, (![B_278]: (k1_relset_1('#skF_2', B_278, '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_3', B_278))), inference(resolution, [status(thm)], [c_4121, c_1142])).
% 16.62/7.89  tff(c_4164, plain, (![B_279]: (k1_relset_1('#skF_2', B_279, '#skF_5')='#skF_2' | ~r1_tarski('#skF_3', B_279))), inference(demodulation, [status(thm), theory('equality')], [c_2326, c_4131])).
% 16.62/7.89  tff(c_4184, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_64, c_4164])).
% 16.62/7.89  tff(c_16690, plain, (![C_638, A_639, B_640, B_641]: (r1_tarski(k2_zfmisc_1(C_638, A_639), k2_zfmisc_1(C_638, B_640)) | ~r1_tarski(B_641, B_640) | ~r1_tarski(A_639, B_641))), inference(resolution, [status(thm)], [c_18, c_4043])).
% 16.62/7.89  tff(c_16792, plain, (![C_638, A_639]: (r1_tarski(k2_zfmisc_1(C_638, A_639), k2_zfmisc_1(C_638, '#skF_4')) | ~r1_tarski(A_639, '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_16690])).
% 16.62/7.89  tff(c_905, plain, (![A_112, C_113, B_114]: (m1_subset_1(A_112, C_113) | ~m1_subset_1(B_114, k1_zfmisc_1(C_113)) | ~r2_hidden(A_112, B_114))), inference(cnfTransformation, [status(thm)], [f_74])).
% 16.62/7.89  tff(c_925, plain, (![A_117, B_118, A_119]: (m1_subset_1(A_117, B_118) | ~r2_hidden(A_117, A_119) | ~r1_tarski(A_119, B_118))), inference(resolution, [status(thm)], [c_30, c_905])).
% 16.62/7.89  tff(c_3216, plain, (![A_249, B_250, B_251]: (m1_subset_1(A_249, B_250) | ~r1_tarski(B_251, B_250) | v1_xboole_0(B_251) | ~m1_subset_1(A_249, B_251))), inference(resolution, [status(thm)], [c_26, c_925])).
% 16.62/7.89  tff(c_3242, plain, (![A_249, B_13, A_12]: (m1_subset_1(A_249, k1_zfmisc_1(B_13)) | v1_xboole_0(k1_zfmisc_1(A_12)) | ~m1_subset_1(A_249, k1_zfmisc_1(A_12)) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_22, c_3216])).
% 16.62/7.89  tff(c_22437, plain, (![A_797, B_798, A_799]: (m1_subset_1(A_797, k1_zfmisc_1(B_798)) | ~m1_subset_1(A_797, k1_zfmisc_1(A_799)) | ~r1_tarski(A_799, B_798))), inference(negUnitSimplification, [status(thm)], [c_24, c_3242])).
% 16.62/7.89  tff(c_22535, plain, (![B_801]: (m1_subset_1('#skF_5', k1_zfmisc_1(B_801)) | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), B_801))), inference(resolution, [status(thm)], [c_66, c_22437])).
% 16.62/7.89  tff(c_22563, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_16792, c_22535])).
% 16.62/7.89  tff(c_22616, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_22563])).
% 16.62/7.89  tff(c_22642, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_2', '#skF_4') | k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2'), inference(resolution, [status(thm)], [c_22616, c_42])).
% 16.62/7.89  tff(c_22666, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4184, c_22642])).
% 16.62/7.89  tff(c_22667, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_119, c_22666])).
% 16.62/7.89  tff(c_2661, plain, (![A_221, B_222, A_223]: (r1_tarski(A_221, k1_zfmisc_1(B_222)) | ~r1_tarski(A_221, k1_zfmisc_1(A_223)) | ~r1_tarski(A_223, B_222))), inference(resolution, [status(thm)], [c_22, c_291])).
% 16.62/7.89  tff(c_15315, plain, (![A_602, B_603, B_604]: (r1_tarski(k1_zfmisc_1(A_602), k1_zfmisc_1(B_603)) | ~r1_tarski(B_604, B_603) | ~r1_tarski(A_602, B_604))), inference(resolution, [status(thm)], [c_22, c_2661])).
% 16.62/7.89  tff(c_15446, plain, (![A_606, A_607]: (r1_tarski(k1_zfmisc_1(A_606), k1_zfmisc_1(A_607)) | ~r1_tarski(A_606, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_15315])).
% 16.62/7.89  tff(c_17209, plain, (![A_653, A_652]: (k1_zfmisc_1(A_653)=k1_zfmisc_1(A_652) | ~r1_tarski(A_652, A_653) | ~r1_tarski(A_653, k1_xboole_0))), inference(resolution, [status(thm)], [c_15446, c_132])).
% 16.62/7.89  tff(c_17315, plain, (k1_zfmisc_1('#skF_3')=k1_zfmisc_1('#skF_4') | ~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_17209])).
% 16.62/7.89  tff(c_17316, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_17315])).
% 16.62/7.89  tff(c_22710, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22667, c_17316])).
% 16.62/7.89  tff(c_22814, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_22710])).
% 16.62/7.89  tff(c_22816, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_17315])).
% 16.62/7.89  tff(c_14166, plain, (![C_580, A_581, B_582, B_583]: (r1_tarski(k2_zfmisc_1(C_580, A_581), k2_zfmisc_1(C_580, B_582)) | ~r1_tarski(B_583, B_582) | ~r1_tarski(A_581, B_583))), inference(resolution, [status(thm)], [c_18, c_4043])).
% 16.62/7.89  tff(c_14349, plain, (![C_592, A_593]: (r1_tarski(k2_zfmisc_1(C_592, A_593), k2_zfmisc_1(C_592, '#skF_4')) | ~r1_tarski(A_593, '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_14166])).
% 16.62/7.89  tff(c_13413, plain, (![A_555, B_556, A_557]: (m1_subset_1(A_555, k1_zfmisc_1(B_556)) | ~m1_subset_1(A_555, k1_zfmisc_1(A_557)) | ~r1_tarski(A_557, B_556))), inference(negUnitSimplification, [status(thm)], [c_24, c_3242])).
% 16.62/7.89  tff(c_13445, plain, (![B_556]: (m1_subset_1('#skF_5', k1_zfmisc_1(B_556)) | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), B_556))), inference(resolution, [status(thm)], [c_66, c_13413])).
% 16.62/7.89  tff(c_14357, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_14349, c_13445])).
% 16.62/7.89  tff(c_14461, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14357])).
% 16.62/7.89  tff(c_14504, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_2', '#skF_4') | k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2'), inference(resolution, [status(thm)], [c_14461, c_42])).
% 16.62/7.89  tff(c_14527, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4184, c_14504])).
% 16.62/7.89  tff(c_14528, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_119, c_14527])).
% 16.62/7.89  tff(c_7876, plain, (![A_385, B_386, B_387]: (r1_tarski(k1_zfmisc_1(A_385), k1_zfmisc_1(B_386)) | ~r1_tarski(B_387, B_386) | ~r1_tarski(A_385, B_387))), inference(resolution, [status(thm)], [c_22, c_2661])).
% 16.62/7.89  tff(c_7946, plain, (![A_388, A_389]: (r1_tarski(k1_zfmisc_1(A_388), k1_zfmisc_1(A_389)) | ~r1_tarski(A_388, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_7876])).
% 16.62/7.89  tff(c_8126, plain, (![A_396, A_395]: (k1_zfmisc_1(A_396)=k1_zfmisc_1(A_395) | ~r1_tarski(A_395, A_396) | ~r1_tarski(A_396, k1_xboole_0))), inference(resolution, [status(thm)], [c_7946, c_132])).
% 16.62/7.89  tff(c_8205, plain, (k1_zfmisc_1('#skF_3')=k1_zfmisc_1('#skF_4') | ~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_8126])).
% 16.62/7.89  tff(c_8206, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_8205])).
% 16.62/7.89  tff(c_14578, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14528, c_8206])).
% 16.62/7.89  tff(c_14674, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_14578])).
% 16.62/7.89  tff(c_14676, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_8205])).
% 16.62/7.89  tff(c_4114, plain, (![B_276]: (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', B_276)) | ~r1_tarski('#skF_3', B_276))), inference(resolution, [status(thm)], [c_113, c_4043])).
% 16.62/7.89  tff(c_14, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 16.62/7.89  tff(c_450, plain, (![A_90, A_91]: (r1_tarski(k2_zfmisc_1(A_90, A_91), k1_xboole_0) | ~r1_tarski(A_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_413])).
% 16.62/7.89  tff(c_7547, plain, (![A_373, A_374, A_375]: (r1_tarski(A_373, k1_xboole_0) | ~r1_tarski(A_373, k2_zfmisc_1(A_374, A_375)) | ~r1_tarski(A_375, k1_xboole_0))), inference(resolution, [status(thm)], [c_450, c_8])).
% 16.62/7.89  tff(c_7655, plain, (![B_276]: (r1_tarski('#skF_5', k1_xboole_0) | ~r1_tarski(B_276, k1_xboole_0) | ~r1_tarski('#skF_3', B_276))), inference(resolution, [status(thm)], [c_4114, c_7547])).
% 16.62/7.89  tff(c_7675, plain, (![B_276]: (~r1_tarski(B_276, k1_xboole_0) | ~r1_tarski('#skF_3', B_276))), inference(splitLeft, [status(thm)], [c_7655])).
% 16.62/7.89  tff(c_14684, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_14676, c_7675])).
% 16.62/7.89  tff(c_14727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_14684])).
% 16.62/7.89  tff(c_14728, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_7655])).
% 16.62/7.89  tff(c_134, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_121])).
% 16.62/7.89  tff(c_14781, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_14728, c_134])).
% 16.62/7.89  tff(c_16, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 16.62/7.89  tff(c_155, plain, (![A_57, B_58]: (m1_subset_1('#skF_1'(A_57, B_58), k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 16.62/7.89  tff(c_166, plain, (![B_59]: (m1_subset_1('#skF_1'(k1_xboole_0, B_59), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_155])).
% 16.62/7.89  tff(c_28, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.62/7.89  tff(c_172, plain, (![B_60]: (r1_tarski('#skF_1'(k1_xboole_0, B_60), k1_xboole_0))), inference(resolution, [status(thm)], [c_166, c_28])).
% 16.62/7.89  tff(c_178, plain, (![B_60]: ('#skF_1'(k1_xboole_0, B_60)=k1_xboole_0)), inference(resolution, [status(thm)], [c_172, c_134])).
% 16.62/7.89  tff(c_161, plain, (![B_8]: (m1_subset_1('#skF_1'(k1_xboole_0, B_8), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_155])).
% 16.62/7.89  tff(c_183, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_161])).
% 16.62/7.89  tff(c_58, plain, (![A_28, B_29]: (m1_subset_1('#skF_1'(A_28, B_29), k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 16.62/7.89  tff(c_1148, plain, (![A_134, B_135]: (k1_relset_1(A_134, B_135, '#skF_1'(A_134, B_135))=k1_relat_1('#skF_1'(A_134, B_135)))), inference(resolution, [status(thm)], [c_58, c_1112])).
% 16.62/7.89  tff(c_1160, plain, (![B_60]: (k1_relat_1('#skF_1'(k1_xboole_0, B_60))=k1_relset_1(k1_xboole_0, B_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_178, c_1148])).
% 16.62/7.89  tff(c_1164, plain, (![B_60]: (k1_relset_1(k1_xboole_0, B_60, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_1160])).
% 16.62/7.89  tff(c_48, plain, (![A_28, B_29]: (v1_funct_2('#skF_1'(A_28, B_29), A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_109])).
% 16.62/7.89  tff(c_44, plain, (![B_26, C_27]: (k1_relset_1(k1_xboole_0, B_26, C_27)=k1_xboole_0 | ~v1_funct_2(C_27, k1_xboole_0, B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_26))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 16.62/7.89  tff(c_1625, plain, (![B_166, C_167]: (k1_relset_1(k1_xboole_0, B_166, C_167)=k1_xboole_0 | ~v1_funct_2(C_167, k1_xboole_0, B_166) | ~m1_subset_1(C_167, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_44])).
% 16.62/7.89  tff(c_1633, plain, (![B_29]: (k1_relset_1(k1_xboole_0, B_29, '#skF_1'(k1_xboole_0, B_29))=k1_xboole_0 | ~m1_subset_1('#skF_1'(k1_xboole_0, B_29), k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_48, c_1625])).
% 16.62/7.89  tff(c_1642, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_183, c_178, c_1164, c_178, c_1633])).
% 16.62/7.89  tff(c_14842, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_14781, c_14781, c_1642])).
% 16.62/7.89  tff(c_14881, plain, ('#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2326, c_14842])).
% 16.62/7.89  tff(c_303, plain, (![A_69]: (r1_tarski(A_69, k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski(A_69, '#skF_5'))), inference(resolution, [status(thm)], [c_113, c_291])).
% 16.62/7.89  tff(c_365, plain, (![A_80, C_81, B_82]: (r1_tarski(k2_zfmisc_1(A_80, C_81), k2_zfmisc_1(B_82, C_81)) | ~r1_tarski(A_80, B_82))), inference(cnfTransformation, [status(thm)], [f_51])).
% 16.62/7.89  tff(c_4429, plain, (![A_289, B_290, C_291, A_292]: (r1_tarski(A_289, k2_zfmisc_1(B_290, C_291)) | ~r1_tarski(A_289, k2_zfmisc_1(A_292, C_291)) | ~r1_tarski(A_292, B_290))), inference(resolution, [status(thm)], [c_365, c_8])).
% 16.62/7.89  tff(c_4513, plain, (![B_293]: (r1_tarski('#skF_5', k2_zfmisc_1(B_293, '#skF_3')) | ~r1_tarski('#skF_2', B_293))), inference(resolution, [status(thm)], [c_113, c_4429])).
% 16.62/7.89  tff(c_4525, plain, (![B_293]: (k1_relset_1(B_293, '#skF_3', '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_2', B_293))), inference(resolution, [status(thm)], [c_4513, c_1142])).
% 16.62/7.89  tff(c_4710, plain, (![B_299]: (k1_relset_1(B_299, '#skF_3', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', B_299))), inference(demodulation, [status(thm), theory('equality')], [c_2326, c_4525])).
% 16.62/7.89  tff(c_4724, plain, (k1_relset_1(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_3', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', '#skF_5')), inference(resolution, [status(thm)], [c_303, c_4710])).
% 16.62/7.89  tff(c_7546, plain, (~r1_tarski('#skF_2', '#skF_5')), inference(splitLeft, [status(thm)], [c_4724])).
% 16.62/7.89  tff(c_14962, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14881, c_7546])).
% 16.62/7.89  tff(c_14997, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_14962])).
% 16.62/7.89  tff(c_14999, plain, (r1_tarski('#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_4724])).
% 16.62/7.89  tff(c_15218, plain, (![A_601]: (r1_tarski(A_601, '#skF_5') | ~r1_tarski(A_601, '#skF_2'))), inference(resolution, [status(thm)], [c_14999, c_8])).
% 16.62/7.89  tff(c_15292, plain, (![A_3, A_601]: (r1_tarski(A_3, '#skF_5') | ~r1_tarski(A_3, A_601) | ~r1_tarski(A_601, '#skF_2'))), inference(resolution, [status(thm)], [c_15218, c_8])).
% 16.62/7.89  tff(c_22826, plain, (r1_tarski('#skF_4', '#skF_5') | ~r1_tarski(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_22816, c_15292])).
% 16.62/7.89  tff(c_22878, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_22826])).
% 16.62/7.89  tff(c_22880, plain, $false, inference(negUnitSimplification, [status(thm)], [c_627, c_22878])).
% 16.62/7.89  tff(c_22881, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_517])).
% 16.62/7.89  tff(c_26674, plain, (![B_972]: (r1_tarski('#skF_3', k2_zfmisc_1('#skF_2', B_972)) | ~r1_tarski('#skF_3', B_972))), inference(resolution, [status(thm)], [c_22881, c_26601])).
% 16.62/7.89  tff(c_304, plain, (![A_69, A_6]: (r1_tarski(A_69, A_6) | ~r1_tarski(A_69, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_291])).
% 16.62/7.89  tff(c_580, plain, (![A_99, A_100, A_101]: (r1_tarski(k2_zfmisc_1(A_99, A_100), A_101) | ~r1_tarski(A_100, k1_xboole_0))), inference(resolution, [status(thm)], [c_450, c_304])).
% 16.62/7.89  tff(c_133, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_113, c_121])).
% 16.62/7.89  tff(c_171, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_133])).
% 16.62/7.89  tff(c_619, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_580, c_171])).
% 16.62/7.89  tff(c_471, plain, (![A_90, A_91]: (k2_zfmisc_1(A_90, A_91)=k1_xboole_0 | ~r1_tarski(A_91, k1_xboole_0))), inference(resolution, [status(thm)], [c_450, c_134])).
% 16.62/7.89  tff(c_613, plain, (![A_90, A_99, A_100]: (k2_zfmisc_1(A_90, k2_zfmisc_1(A_99, A_100))=k1_xboole_0 | ~r1_tarski(A_100, k1_xboole_0))), inference(resolution, [status(thm)], [c_580, c_471])).
% 16.62/7.89  tff(c_26987, plain, (![B_982]: (r1_tarski('#skF_3', k2_zfmisc_1('#skF_2', B_982)) | ~r1_tarski('#skF_3', B_982))), inference(resolution, [status(thm)], [c_22881, c_26601])).
% 16.62/7.89  tff(c_27022, plain, (![A_99, A_100]: (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', k2_zfmisc_1(A_99, A_100)) | ~r1_tarski(A_100, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_613, c_26987])).
% 16.62/7.89  tff(c_27242, plain, (![A_989, A_990]: (~r1_tarski('#skF_3', k2_zfmisc_1(A_989, A_990)) | ~r1_tarski(A_990, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_619, c_27022])).
% 16.62/7.89  tff(c_27286, plain, (![B_972]: (~r1_tarski(B_972, k1_xboole_0) | ~r1_tarski('#skF_3', B_972))), inference(resolution, [status(thm)], [c_26674, c_27242])).
% 16.62/7.89  tff(c_40605, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40589, c_27286])).
% 16.62/7.89  tff(c_40659, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_40605])).
% 16.62/7.89  tff(c_40660, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_133])).
% 16.62/7.89  tff(c_40677, plain, (![B_1324, A_1325]: (k1_xboole_0=B_1324 | k1_xboole_0=A_1325 | k2_zfmisc_1(A_1325, B_1324)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 16.62/7.89  tff(c_40680, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_40660, c_40677])).
% 16.62/7.89  tff(c_40687, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_104, c_40680])).
% 16.62/7.89  tff(c_40692, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_40687])).
% 16.62/7.89  tff(c_40663, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40660, c_66])).
% 16.62/7.89  tff(c_41677, plain, (![A_1391, B_1392, C_1393]: (k1_relset_1(A_1391, B_1392, C_1393)=k1_relat_1(C_1393) | ~m1_subset_1(C_1393, k1_zfmisc_1(k2_zfmisc_1(A_1391, B_1392))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 16.62/7.89  tff(c_41709, plain, (![C_1394]: (k1_relset_1('#skF_2', '#skF_3', C_1394)=k1_relat_1(C_1394) | ~m1_subset_1(C_1394, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_40660, c_41677])).
% 16.62/7.89  tff(c_41721, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40663, c_41709])).
% 16.62/7.89  tff(c_42971, plain, (![B_1468, A_1469, C_1470]: (k1_xboole_0=B_1468 | k1_relset_1(A_1469, B_1468, C_1470)=A_1469 | ~v1_funct_2(C_1470, A_1469, B_1468) | ~m1_subset_1(C_1470, k1_zfmisc_1(k2_zfmisc_1(A_1469, B_1468))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 16.62/7.89  tff(c_42986, plain, (![C_1470]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_1470)='#skF_2' | ~v1_funct_2(C_1470, '#skF_2', '#skF_3') | ~m1_subset_1(C_1470, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_40660, c_42971])).
% 16.62/7.89  tff(c_43177, plain, (![C_1480]: (k1_relset_1('#skF_2', '#skF_3', C_1480)='#skF_2' | ~v1_funct_2(C_1480, '#skF_2', '#skF_3') | ~m1_subset_1(C_1480, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_104, c_42986])).
% 16.62/7.89  tff(c_43183, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40663, c_43177])).
% 16.62/7.89  tff(c_43193, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_41721, c_43183])).
% 16.62/7.89  tff(c_40833, plain, (![C_1338, A_1339, B_1340]: (r1_tarski(k2_zfmisc_1(C_1338, A_1339), k2_zfmisc_1(C_1338, B_1340)) | ~r1_tarski(A_1339, B_1340))), inference(cnfTransformation, [status(thm)], [f_51])).
% 16.62/7.89  tff(c_40840, plain, (![B_1340]: (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', B_1340)) | ~r1_tarski('#skF_3', B_1340))), inference(superposition, [status(thm), theory('equality')], [c_40660, c_40833])).
% 16.62/7.89  tff(c_43418, plain, (![A_1489, B_1490, A_1491]: (k1_relset_1(A_1489, B_1490, A_1491)=k1_relat_1(A_1491) | ~r1_tarski(A_1491, k2_zfmisc_1(A_1489, B_1490)))), inference(resolution, [status(thm)], [c_30, c_41677])).
% 16.62/7.89  tff(c_43462, plain, (![B_1340]: (k1_relset_1('#skF_2', B_1340, '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_3', B_1340))), inference(resolution, [status(thm)], [c_40840, c_43418])).
% 16.62/7.89  tff(c_43525, plain, (![B_1495]: (k1_relset_1('#skF_2', B_1495, '#skF_5')='#skF_2' | ~r1_tarski('#skF_3', B_1495))), inference(demodulation, [status(thm), theory('equality')], [c_43193, c_43462])).
% 16.62/7.89  tff(c_43540, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_64, c_43525])).
% 16.62/7.89  tff(c_45991, plain, (![A_1579, C_1580, B_1581, A_1582]: (r1_tarski(A_1579, k2_zfmisc_1(C_1580, B_1581)) | ~r1_tarski(A_1579, k2_zfmisc_1(C_1580, A_1582)) | ~r1_tarski(A_1582, B_1581))), inference(resolution, [status(thm)], [c_40833, c_8])).
% 16.62/7.89  tff(c_52964, plain, (![C_1784, A_1785, B_1786, B_1787]: (r1_tarski(k2_zfmisc_1(C_1784, A_1785), k2_zfmisc_1(C_1784, B_1786)) | ~r1_tarski(B_1787, B_1786) | ~r1_tarski(A_1785, B_1787))), inference(resolution, [status(thm)], [c_18, c_45991])).
% 16.62/7.89  tff(c_53071, plain, (![C_1788, A_1789]: (r1_tarski(k2_zfmisc_1(C_1788, A_1789), k2_zfmisc_1(C_1788, '#skF_4')) | ~r1_tarski(A_1789, '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_52964])).
% 16.62/7.89  tff(c_53162, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40660, c_53071])).
% 16.62/7.89  tff(c_53203, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_53162])).
% 16.62/7.89  tff(c_42476, plain, (![B_1446, C_1447, A_1448]: (k1_xboole_0=B_1446 | v1_funct_2(C_1447, A_1448, B_1446) | k1_relset_1(A_1448, B_1446, C_1447)!=A_1448 | ~m1_subset_1(C_1447, k1_zfmisc_1(k2_zfmisc_1(A_1448, B_1446))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 16.62/7.89  tff(c_42508, plain, (![B_1446, A_17, A_1448]: (k1_xboole_0=B_1446 | v1_funct_2(A_17, A_1448, B_1446) | k1_relset_1(A_1448, B_1446, A_17)!=A_1448 | ~r1_tarski(A_17, k2_zfmisc_1(A_1448, B_1446)))), inference(resolution, [status(thm)], [c_30, c_42476])).
% 16.62/7.89  tff(c_53228, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_2', '#skF_4') | k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2'), inference(resolution, [status(thm)], [c_53203, c_42508])).
% 16.62/7.89  tff(c_53260, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_43540, c_53228])).
% 16.62/7.89  tff(c_53261, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_119, c_53260])).
% 16.62/7.89  tff(c_40732, plain, (![A_1329, C_1330, B_1331]: (r1_tarski(A_1329, C_1330) | ~r1_tarski(B_1331, C_1330) | ~r1_tarski(A_1329, B_1331))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.62/7.89  tff(c_43858, plain, (![A_1510, B_1511, A_1512]: (r1_tarski(A_1510, k1_zfmisc_1(B_1511)) | ~r1_tarski(A_1510, k1_zfmisc_1(A_1512)) | ~r1_tarski(A_1512, B_1511))), inference(resolution, [status(thm)], [c_22, c_40732])).
% 16.62/7.89  tff(c_50092, plain, (![A_1690, B_1691, B_1692]: (r1_tarski(k1_zfmisc_1(A_1690), k1_zfmisc_1(B_1691)) | ~r1_tarski(B_1692, B_1691) | ~r1_tarski(A_1690, B_1692))), inference(resolution, [status(thm)], [c_22, c_43858])).
% 16.62/7.89  tff(c_50186, plain, (![A_1693, A_1694]: (r1_tarski(k1_zfmisc_1(A_1693), k1_zfmisc_1(A_1694)) | ~r1_tarski(A_1693, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_50092])).
% 16.62/7.89  tff(c_50258, plain, (![A_1697, A_1696]: (k1_zfmisc_1(A_1697)=k1_zfmisc_1(A_1696) | ~r1_tarski(A_1696, A_1697) | ~r1_tarski(A_1697, k1_xboole_0))), inference(resolution, [status(thm)], [c_50186, c_132])).
% 16.62/7.89  tff(c_50362, plain, (k1_zfmisc_1('#skF_3')=k1_zfmisc_1('#skF_4') | ~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_50258])).
% 16.62/7.89  tff(c_50363, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_50362])).
% 16.62/7.89  tff(c_53300, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_53261, c_50363])).
% 16.62/7.89  tff(c_53408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_53300])).
% 16.62/7.89  tff(c_53410, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_50362])).
% 16.62/7.89  tff(c_40912, plain, (![A_1346, A_1347]: (r1_tarski(k2_zfmisc_1(A_1346, A_1347), k1_xboole_0) | ~r1_tarski(A_1347, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_40833])).
% 16.62/7.89  tff(c_44001, plain, (![A_1517, A_1518, A_1519]: (r1_tarski(A_1517, k1_xboole_0) | ~r1_tarski(A_1517, k2_zfmisc_1(A_1518, A_1519)) | ~r1_tarski(A_1519, k1_xboole_0))), inference(resolution, [status(thm)], [c_40912, c_8])).
% 16.62/7.89  tff(c_44082, plain, (![B_1340]: (r1_tarski('#skF_5', k1_xboole_0) | ~r1_tarski(B_1340, k1_xboole_0) | ~r1_tarski('#skF_3', B_1340))), inference(resolution, [status(thm)], [c_40840, c_44001])).
% 16.62/7.89  tff(c_44732, plain, (![B_1340]: (~r1_tarski(B_1340, k1_xboole_0) | ~r1_tarski('#skF_3', B_1340))), inference(splitLeft, [status(thm)], [c_44082])).
% 16.62/7.89  tff(c_53423, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_53410, c_44732])).
% 16.62/7.89  tff(c_53455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_53423])).
% 16.62/7.89  tff(c_53456, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_44082])).
% 16.62/7.89  tff(c_53473, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_53456, c_134])).
% 16.62/7.89  tff(c_53488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40692, c_53473])).
% 16.62/7.89  tff(c_53489, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_40687])).
% 16.62/7.89  tff(c_53497, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_53489, c_10])).
% 16.62/7.89  tff(c_170, plain, (![B_59]: (r1_tarski('#skF_1'(k1_xboole_0, B_59), k1_xboole_0))), inference(resolution, [status(thm)], [c_166, c_28])).
% 16.62/7.89  tff(c_53574, plain, (![B_1797]: (r1_tarski('#skF_1'('#skF_2', B_1797), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_53489, c_53489, c_170])).
% 16.62/7.89  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.62/7.89  tff(c_53578, plain, (![B_1797]: ('#skF_1'('#skF_2', B_1797)='#skF_2' | ~r1_tarski('#skF_2', '#skF_1'('#skF_2', B_1797)))), inference(resolution, [status(thm)], [c_53574, c_2])).
% 16.62/7.89  tff(c_53585, plain, (![B_1798]: ('#skF_1'('#skF_2', B_1798)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_53497, c_53578])).
% 16.62/7.89  tff(c_53593, plain, (![B_1798]: (v1_funct_2('#skF_2', '#skF_2', B_1798))), inference(superposition, [status(thm), theory('equality')], [c_53585, c_48])).
% 16.62/7.89  tff(c_53490, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_40687])).
% 16.62/7.89  tff(c_53512, plain, ('#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_53489, c_53490])).
% 16.62/7.89  tff(c_53515, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_53512, c_119])).
% 16.62/7.89  tff(c_53627, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53593, c_53515])).
% 16.62/7.89  tff(c_53628, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_72])).
% 16.62/7.89  tff(c_53633, plain, (~r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_53628])).
% 16.62/7.89  tff(c_58852, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58831, c_53633])).
% 16.62/7.89  tff(c_58882, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_58852])).
% 16.62/7.89  tff(c_58884, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_62])).
% 16.62/7.89  tff(c_58883, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_62])).
% 16.62/7.89  tff(c_58892, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58884, c_58883])).
% 16.62/7.89  tff(c_58885, plain, (![B_8]: (k2_zfmisc_1('#skF_2', B_8)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58883, c_58883, c_16])).
% 16.62/7.89  tff(c_58915, plain, (![B_8]: (k2_zfmisc_1('#skF_3', B_8)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58892, c_58892, c_58885])).
% 16.62/7.89  tff(c_59007, plain, (![A_2086, B_2087]: (m1_subset_1('#skF_1'(A_2086, B_2087), k1_zfmisc_1(k2_zfmisc_1(A_2086, B_2087))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 16.62/7.89  tff(c_59028, plain, (![B_2091]: (m1_subset_1('#skF_1'('#skF_3', B_2091), k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_58915, c_59007])).
% 16.62/7.89  tff(c_59033, plain, (![B_2092]: (r1_tarski('#skF_1'('#skF_3', B_2092), '#skF_3'))), inference(resolution, [status(thm)], [c_59028, c_28])).
% 16.62/7.89  tff(c_58887, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_58883, c_10])).
% 16.62/7.89  tff(c_58903, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_58892, c_58887])).
% 16.62/7.89  tff(c_58947, plain, (![B_2077, A_2078]: (B_2077=A_2078 | ~r1_tarski(B_2077, A_2078) | ~r1_tarski(A_2078, B_2077))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.62/7.89  tff(c_58957, plain, (![A_6]: (A_6='#skF_3' | ~r1_tarski(A_6, '#skF_3'))), inference(resolution, [status(thm)], [c_58903, c_58947])).
% 16.62/7.89  tff(c_59050, plain, (![B_2093]: ('#skF_1'('#skF_3', B_2093)='#skF_3')), inference(resolution, [status(thm)], [c_59033, c_58957])).
% 16.62/7.89  tff(c_59058, plain, (![B_2093]: (v1_funct_2('#skF_3', '#skF_3', B_2093))), inference(superposition, [status(thm), theory('equality')], [c_59050, c_48])).
% 16.62/7.89  tff(c_58886, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58883, c_58883, c_14])).
% 16.62/7.89  tff(c_58906, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58892, c_58892, c_58886])).
% 16.62/7.89  tff(c_58897, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58892, c_66])).
% 16.62/7.89  tff(c_58933, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58906, c_58897])).
% 16.62/7.89  tff(c_58937, plain, (![A_2073, B_2074]: (r1_tarski(A_2073, B_2074) | ~m1_subset_1(A_2073, k1_zfmisc_1(B_2074)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.62/7.89  tff(c_58941, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_58933, c_58937])).
% 16.62/7.89  tff(c_58949, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_58941, c_58947])).
% 16.62/7.89  tff(c_58956, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58903, c_58949])).
% 16.62/7.89  tff(c_58935, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58892, c_58933, c_58915, c_58892, c_72])).
% 16.62/7.89  tff(c_58975, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58956, c_58935])).
% 16.62/7.89  tff(c_59103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59058, c_58975])).
% 16.62/7.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.62/7.89  
% 16.62/7.89  Inference rules
% 16.62/7.89  ----------------------
% 16.62/7.89  #Ref     : 0
% 16.62/7.89  #Sup     : 14872
% 16.62/7.89  #Fact    : 0
% 16.62/7.89  #Define  : 0
% 16.62/7.89  #Split   : 65
% 16.62/7.89  #Chain   : 0
% 16.62/7.89  #Close   : 0
% 16.62/7.89  
% 16.62/7.89  Ordering : KBO
% 16.62/7.89  
% 16.62/7.89  Simplification rules
% 16.62/7.89  ----------------------
% 16.62/7.89  #Subsume      : 3899
% 16.62/7.89  #Demod        : 9175
% 16.62/7.89  #Tautology    : 5669
% 16.62/7.89  #SimpNegUnit  : 193
% 16.62/7.89  #BackRed      : 731
% 16.62/7.89  
% 16.62/7.89  #Partial instantiations: 0
% 16.62/7.89  #Strategies tried      : 1
% 16.62/7.89  
% 16.62/7.89  Timing (in seconds)
% 16.62/7.89  ----------------------
% 16.62/7.89  Preprocessing        : 0.34
% 16.62/7.89  Parsing              : 0.18
% 16.62/7.89  CNF conversion       : 0.02
% 16.62/7.89  Main loop            : 6.71
% 16.62/7.89  Inferencing          : 1.46
% 16.62/7.89  Reduction            : 2.30
% 16.62/7.89  Demodulation         : 1.69
% 16.62/7.89  BG Simplification    : 0.17
% 16.62/7.89  Subsumption          : 2.29
% 16.62/7.89  Abstraction          : 0.24
% 16.62/7.89  MUC search           : 0.00
% 16.62/7.89  Cooper               : 0.00
% 16.62/7.89  Total                : 7.15
% 16.62/7.89  Index Insertion      : 0.00
% 16.62/7.89  Index Deletion       : 0.00
% 16.62/7.89  Index Matching       : 0.00
% 16.62/7.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
