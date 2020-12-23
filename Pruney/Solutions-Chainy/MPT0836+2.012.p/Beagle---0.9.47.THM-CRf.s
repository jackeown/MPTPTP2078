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
% DateTime   : Thu Dec  3 10:08:04 EST 2020

% Result     : Theorem 15.95s
% Output     : CNFRefutation 15.95s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 136 expanded)
%              Number of leaves         :   26 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :  115 ( 331 expanded)
%              Number of equality atoms :    8 (  20 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_25000,plain,(
    ! [A_1167,B_1168,C_1169] :
      ( k1_relset_1(A_1167,B_1168,C_1169) = k1_relat_1(C_1169)
      | ~ m1_subset_1(C_1169,k1_zfmisc_1(k2_zfmisc_1(A_1167,B_1168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_25009,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_25000])).

tff(c_2805,plain,(
    ! [A_352,B_353,C_354] :
      ( k1_relset_1(A_352,B_353,C_354) = k1_relat_1(C_354)
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(A_352,B_353))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2814,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_2805])).

tff(c_50,plain,
    ( r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7'))
    | m1_subset_1('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_67,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_46,plain,
    ( r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7'))
    | r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_97,plain,(
    r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_20,plain,(
    ! [C_26,A_11,D_29] :
      ( r2_hidden(C_26,k1_relat_1(A_11))
      | ~ r2_hidden(k4_tarski(C_26,D_29),A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_107,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_97,c_20])).

tff(c_126,plain,(
    ! [A_98,B_99,C_100] :
      ( k1_relset_1(A_98,B_99,C_100) = k1_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_135,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_126])).

tff(c_40,plain,(
    ! [E_74] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_74),'#skF_7')
      | ~ m1_subset_1(E_74,'#skF_6')
      | ~ r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_233,plain,(
    ! [E_114] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_114),'#skF_7')
      | ~ m1_subset_1(E_114,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_135,c_40])).

tff(c_240,plain,(
    ~ m1_subset_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_97,c_233])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_240])).

tff(c_251,plain,(
    r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2817,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2814,c_251])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2856,plain,(
    ! [C_361,A_362] :
      ( r2_hidden(k4_tarski(C_361,'#skF_4'(A_362,k1_relat_1(A_362),C_361)),A_362)
      | ~ r2_hidden(C_361,k1_relat_1(A_362)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [C_10,A_7,B_8] :
      ( r2_hidden(C_10,A_7)
      | ~ r2_hidden(C_10,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6846,plain,(
    ! [C_595,A_596,A_597] :
      ( r2_hidden(k4_tarski(C_595,'#skF_4'(A_596,k1_relat_1(A_596),C_595)),A_597)
      | ~ m1_subset_1(A_596,k1_zfmisc_1(A_597))
      | ~ r2_hidden(C_595,k1_relat_1(A_596)) ) ),
    inference(resolution,[status(thm)],[c_2856,c_16])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_21562,plain,(
    ! [A_867,C_868,D_869,C_870] :
      ( r2_hidden('#skF_4'(A_867,k1_relat_1(A_867),C_868),D_869)
      | ~ m1_subset_1(A_867,k1_zfmisc_1(k2_zfmisc_1(C_870,D_869)))
      | ~ r2_hidden(C_868,k1_relat_1(A_867)) ) ),
    inference(resolution,[status(thm)],[c_6846,c_4])).

tff(c_21594,plain,(
    ! [C_871] :
      ( r2_hidden('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_871),'#skF_6')
      | ~ r2_hidden(C_871,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_34,c_21562])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_21631,plain,(
    ! [C_871] :
      ( m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_871),'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ r2_hidden(C_871,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_21594,c_8])).

tff(c_21652,plain,(
    ! [C_872] :
      ( m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_872),'#skF_6')
      | ~ r2_hidden(C_872,k1_relat_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_21631])).

tff(c_252,plain,(
    ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,(
    ! [E_74] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_74),'#skF_7')
      | ~ m1_subset_1(E_74,'#skF_6')
      | r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2795,plain,(
    ! [E_74] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_74),'#skF_7')
      | ~ m1_subset_1(E_74,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_252,c_44])).

tff(c_2860,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_8'),'#skF_6')
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2856,c_2795])).

tff(c_2879,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2817,c_2860])).

tff(c_21661,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_21652,c_2879])).

tff(c_21673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2817,c_21661])).

tff(c_21674,plain,(
    r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_25012,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25009,c_21674])).

tff(c_25100,plain,(
    ! [C_1186,A_1187] :
      ( r2_hidden(k4_tarski(C_1186,'#skF_4'(A_1187,k1_relat_1(A_1187),C_1186)),A_1187)
      | ~ r2_hidden(C_1186,k1_relat_1(A_1187)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_27452,plain,(
    ! [C_1351,A_1352,A_1353] :
      ( r2_hidden(k4_tarski(C_1351,'#skF_4'(A_1352,k1_relat_1(A_1352),C_1351)),A_1353)
      | ~ m1_subset_1(A_1352,k1_zfmisc_1(A_1353))
      | ~ r2_hidden(C_1351,k1_relat_1(A_1352)) ) ),
    inference(resolution,[status(thm)],[c_25100,c_16])).

tff(c_45765,plain,(
    ! [A_1719,C_1720,D_1721,C_1722] :
      ( r2_hidden('#skF_4'(A_1719,k1_relat_1(A_1719),C_1720),D_1721)
      | ~ m1_subset_1(A_1719,k1_zfmisc_1(k2_zfmisc_1(C_1722,D_1721)))
      | ~ r2_hidden(C_1720,k1_relat_1(A_1719)) ) ),
    inference(resolution,[status(thm)],[c_27452,c_4])).

tff(c_45797,plain,(
    ! [C_1723] :
      ( r2_hidden('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_1723),'#skF_6')
      | ~ r2_hidden(C_1723,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_34,c_45765])).

tff(c_45834,plain,(
    ! [C_1723] :
      ( m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_1723),'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ r2_hidden(C_1723,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_45797,c_8])).

tff(c_45855,plain,(
    ! [C_1724] :
      ( m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_1724),'#skF_6')
      | ~ r2_hidden(C_1724,k1_relat_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_45834])).

tff(c_21675,plain,(
    ~ m1_subset_1('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [E_74] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_74),'#skF_7')
      | ~ m1_subset_1(E_74,'#skF_6')
      | m1_subset_1('#skF_9','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_21680,plain,(
    ! [E_74] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_74),'#skF_7')
      | ~ m1_subset_1(E_74,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_21675,c_48])).

tff(c_25119,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_8'),'#skF_6')
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_25100,c_21680])).

tff(c_25130,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25012,c_25119])).

tff(c_45864,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_45855,c_25130])).

tff(c_45876,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25012,c_45864])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.95/7.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.95/7.88  
% 15.95/7.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.95/7.88  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 15.95/7.88  
% 15.95/7.88  %Foreground sorts:
% 15.95/7.88  
% 15.95/7.88  
% 15.95/7.88  %Background operators:
% 15.95/7.88  
% 15.95/7.88  
% 15.95/7.88  %Foreground operators:
% 15.95/7.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.95/7.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.95/7.88  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 15.95/7.88  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 15.95/7.88  tff('#skF_7', type, '#skF_7': $i).
% 15.95/7.88  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 15.95/7.88  tff('#skF_5', type, '#skF_5': $i).
% 15.95/7.88  tff('#skF_6', type, '#skF_6': $i).
% 15.95/7.88  tff('#skF_9', type, '#skF_9': $i).
% 15.95/7.88  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 15.95/7.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.95/7.88  tff('#skF_8', type, '#skF_8': $i).
% 15.95/7.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.95/7.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.95/7.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.95/7.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.95/7.88  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.95/7.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.95/7.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.95/7.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.95/7.88  
% 15.95/7.90  tff(f_84, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, A) => (r2_hidden(D, k1_relset_1(A, B, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(D, E), C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relset_1)).
% 15.95/7.90  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 15.95/7.90  tff(f_59, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 15.95/7.90  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 15.95/7.90  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 15.95/7.90  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 15.95/7.90  tff(c_34, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 15.95/7.90  tff(c_25000, plain, (![A_1167, B_1168, C_1169]: (k1_relset_1(A_1167, B_1168, C_1169)=k1_relat_1(C_1169) | ~m1_subset_1(C_1169, k1_zfmisc_1(k2_zfmisc_1(A_1167, B_1168))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.95/7.90  tff(c_25009, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_34, c_25000])).
% 15.95/7.90  tff(c_2805, plain, (![A_352, B_353, C_354]: (k1_relset_1(A_352, B_353, C_354)=k1_relat_1(C_354) | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(A_352, B_353))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.95/7.90  tff(c_2814, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_34, c_2805])).
% 15.95/7.90  tff(c_50, plain, (r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7')) | m1_subset_1('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 15.95/7.90  tff(c_67, plain, (m1_subset_1('#skF_9', '#skF_6')), inference(splitLeft, [status(thm)], [c_50])).
% 15.95/7.90  tff(c_46, plain, (r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7')) | r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_84])).
% 15.95/7.90  tff(c_97, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_7')), inference(splitLeft, [status(thm)], [c_46])).
% 15.95/7.90  tff(c_20, plain, (![C_26, A_11, D_29]: (r2_hidden(C_26, k1_relat_1(A_11)) | ~r2_hidden(k4_tarski(C_26, D_29), A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.95/7.90  tff(c_107, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_97, c_20])).
% 15.95/7.90  tff(c_126, plain, (![A_98, B_99, C_100]: (k1_relset_1(A_98, B_99, C_100)=k1_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.95/7.90  tff(c_135, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_34, c_126])).
% 15.95/7.90  tff(c_40, plain, (![E_74]: (~r2_hidden(k4_tarski('#skF_8', E_74), '#skF_7') | ~m1_subset_1(E_74, '#skF_6') | ~r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 15.95/7.90  tff(c_233, plain, (![E_114]: (~r2_hidden(k4_tarski('#skF_8', E_114), '#skF_7') | ~m1_subset_1(E_114, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_135, c_40])).
% 15.95/7.90  tff(c_240, plain, (~m1_subset_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_97, c_233])).
% 15.95/7.90  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_240])).
% 15.95/7.90  tff(c_251, plain, (r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_46])).
% 15.95/7.90  tff(c_2817, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2814, c_251])).
% 15.95/7.90  tff(c_36, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 15.95/7.90  tff(c_2856, plain, (![C_361, A_362]: (r2_hidden(k4_tarski(C_361, '#skF_4'(A_362, k1_relat_1(A_362), C_361)), A_362) | ~r2_hidden(C_361, k1_relat_1(A_362)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.95/7.90  tff(c_16, plain, (![C_10, A_7, B_8]: (r2_hidden(C_10, A_7) | ~r2_hidden(C_10, B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.95/7.90  tff(c_6846, plain, (![C_595, A_596, A_597]: (r2_hidden(k4_tarski(C_595, '#skF_4'(A_596, k1_relat_1(A_596), C_595)), A_597) | ~m1_subset_1(A_596, k1_zfmisc_1(A_597)) | ~r2_hidden(C_595, k1_relat_1(A_596)))), inference(resolution, [status(thm)], [c_2856, c_16])).
% 15.95/7.90  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.95/7.90  tff(c_21562, plain, (![A_867, C_868, D_869, C_870]: (r2_hidden('#skF_4'(A_867, k1_relat_1(A_867), C_868), D_869) | ~m1_subset_1(A_867, k1_zfmisc_1(k2_zfmisc_1(C_870, D_869))) | ~r2_hidden(C_868, k1_relat_1(A_867)))), inference(resolution, [status(thm)], [c_6846, c_4])).
% 15.95/7.90  tff(c_21594, plain, (![C_871]: (r2_hidden('#skF_4'('#skF_7', k1_relat_1('#skF_7'), C_871), '#skF_6') | ~r2_hidden(C_871, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_34, c_21562])).
% 15.95/7.90  tff(c_8, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 15.95/7.90  tff(c_21631, plain, (![C_871]: (m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), C_871), '#skF_6') | v1_xboole_0('#skF_6') | ~r2_hidden(C_871, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_21594, c_8])).
% 15.95/7.90  tff(c_21652, plain, (![C_872]: (m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), C_872), '#skF_6') | ~r2_hidden(C_872, k1_relat_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_36, c_21631])).
% 15.95/7.90  tff(c_252, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_7')), inference(splitRight, [status(thm)], [c_46])).
% 15.95/7.90  tff(c_44, plain, (![E_74]: (~r2_hidden(k4_tarski('#skF_8', E_74), '#skF_7') | ~m1_subset_1(E_74, '#skF_6') | r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 15.95/7.90  tff(c_2795, plain, (![E_74]: (~r2_hidden(k4_tarski('#skF_8', E_74), '#skF_7') | ~m1_subset_1(E_74, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_252, c_44])).
% 15.95/7.90  tff(c_2860, plain, (~m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), '#skF_8'), '#skF_6') | ~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_2856, c_2795])).
% 15.95/7.90  tff(c_2879, plain, (~m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2817, c_2860])).
% 15.95/7.90  tff(c_21661, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_21652, c_2879])).
% 15.95/7.90  tff(c_21673, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2817, c_21661])).
% 15.95/7.90  tff(c_21674, plain, (r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_50])).
% 15.95/7.90  tff(c_25012, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_25009, c_21674])).
% 15.95/7.90  tff(c_25100, plain, (![C_1186, A_1187]: (r2_hidden(k4_tarski(C_1186, '#skF_4'(A_1187, k1_relat_1(A_1187), C_1186)), A_1187) | ~r2_hidden(C_1186, k1_relat_1(A_1187)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.95/7.90  tff(c_27452, plain, (![C_1351, A_1352, A_1353]: (r2_hidden(k4_tarski(C_1351, '#skF_4'(A_1352, k1_relat_1(A_1352), C_1351)), A_1353) | ~m1_subset_1(A_1352, k1_zfmisc_1(A_1353)) | ~r2_hidden(C_1351, k1_relat_1(A_1352)))), inference(resolution, [status(thm)], [c_25100, c_16])).
% 15.95/7.90  tff(c_45765, plain, (![A_1719, C_1720, D_1721, C_1722]: (r2_hidden('#skF_4'(A_1719, k1_relat_1(A_1719), C_1720), D_1721) | ~m1_subset_1(A_1719, k1_zfmisc_1(k2_zfmisc_1(C_1722, D_1721))) | ~r2_hidden(C_1720, k1_relat_1(A_1719)))), inference(resolution, [status(thm)], [c_27452, c_4])).
% 15.95/7.90  tff(c_45797, plain, (![C_1723]: (r2_hidden('#skF_4'('#skF_7', k1_relat_1('#skF_7'), C_1723), '#skF_6') | ~r2_hidden(C_1723, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_34, c_45765])).
% 15.95/7.90  tff(c_45834, plain, (![C_1723]: (m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), C_1723), '#skF_6') | v1_xboole_0('#skF_6') | ~r2_hidden(C_1723, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_45797, c_8])).
% 15.95/7.90  tff(c_45855, plain, (![C_1724]: (m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), C_1724), '#skF_6') | ~r2_hidden(C_1724, k1_relat_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_36, c_45834])).
% 15.95/7.90  tff(c_21675, plain, (~m1_subset_1('#skF_9', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 15.95/7.90  tff(c_48, plain, (![E_74]: (~r2_hidden(k4_tarski('#skF_8', E_74), '#skF_7') | ~m1_subset_1(E_74, '#skF_6') | m1_subset_1('#skF_9', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 15.95/7.90  tff(c_21680, plain, (![E_74]: (~r2_hidden(k4_tarski('#skF_8', E_74), '#skF_7') | ~m1_subset_1(E_74, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_21675, c_48])).
% 15.95/7.90  tff(c_25119, plain, (~m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), '#skF_8'), '#skF_6') | ~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_25100, c_21680])).
% 15.95/7.90  tff(c_25130, plain, (~m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_25012, c_25119])).
% 15.95/7.90  tff(c_45864, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_45855, c_25130])).
% 15.95/7.90  tff(c_45876, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25012, c_45864])).
% 15.95/7.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.95/7.90  
% 15.95/7.90  Inference rules
% 15.95/7.90  ----------------------
% 15.95/7.90  #Ref     : 0
% 15.95/7.90  #Sup     : 12324
% 15.95/7.90  #Fact    : 0
% 15.95/7.90  #Define  : 0
% 15.95/7.90  #Split   : 25
% 15.95/7.90  #Chain   : 0
% 15.95/7.90  #Close   : 0
% 15.95/7.90  
% 15.95/7.90  Ordering : KBO
% 15.95/7.90  
% 15.95/7.90  Simplification rules
% 15.95/7.90  ----------------------
% 15.95/7.90  #Subsume      : 429
% 15.95/7.90  #Demod        : 178
% 15.95/7.90  #Tautology    : 284
% 15.95/7.90  #SimpNegUnit  : 66
% 15.95/7.90  #BackRed      : 91
% 15.95/7.90  
% 15.95/7.90  #Partial instantiations: 0
% 15.95/7.90  #Strategies tried      : 1
% 15.95/7.90  
% 15.95/7.90  Timing (in seconds)
% 15.95/7.90  ----------------------
% 15.95/7.90  Preprocessing        : 0.42
% 15.95/7.90  Parsing              : 0.24
% 15.95/7.90  CNF conversion       : 0.03
% 15.95/7.90  Main loop            : 6.70
% 15.95/7.90  Inferencing          : 1.20
% 15.95/7.90  Reduction            : 1.33
% 15.95/7.90  Demodulation         : 0.84
% 15.95/7.90  BG Simplification    : 0.24
% 15.95/7.90  Subsumption          : 3.32
% 15.95/7.90  Abstraction          : 0.31
% 15.95/7.90  MUC search           : 0.00
% 15.95/7.90  Cooper               : 0.00
% 15.95/7.90  Total                : 7.16
% 15.95/7.90  Index Insertion      : 0.00
% 15.95/7.90  Index Deletion       : 0.00
% 15.95/7.90  Index Matching       : 0.00
% 15.95/7.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
