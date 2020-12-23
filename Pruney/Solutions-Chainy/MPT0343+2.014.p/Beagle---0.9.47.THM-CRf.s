%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:18 EST 2020

% Result     : Theorem 27.54s
% Output     : CNFRefutation 27.75s
% Verified   : 
% Statistics : Number of formulae       :  242 (3460 expanded)
%              Number of leaves         :   28 (1076 expanded)
%              Depth                    :   26
%              Number of atoms          :  522 (9613 expanded)
%              Number of equality atoms :   62 ( 782 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,A)
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_75,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_59,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(c_50,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_52,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_54,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_48,plain,(
    ! [A_31,B_32,C_36] :
      ( m1_subset_1('#skF_6'(A_31,B_32,C_36),A_31)
      | r1_tarski(B_32,C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(A_31))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_104274,plain,(
    ! [A_2131,B_2132,C_2133] :
      ( r2_hidden('#skF_6'(A_2131,B_2132,C_2133),B_2132)
      | r1_tarski(B_2132,C_2133)
      | ~ m1_subset_1(C_2133,k1_zfmisc_1(A_2131))
      | ~ m1_subset_1(B_2132,k1_zfmisc_1(A_2131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_89166,plain,(
    ! [A_1844,B_1845,C_1846] :
      ( r2_hidden('#skF_6'(A_1844,B_1845,C_1846),B_1845)
      | r1_tarski(B_1845,C_1846)
      | ~ m1_subset_1(C_1846,k1_zfmisc_1(A_1844))
      | ~ m1_subset_1(B_1845,k1_zfmisc_1(A_1844)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_73,plain,(
    ! [D_52] :
      ( r2_hidden(D_52,'#skF_9')
      | ~ r2_hidden(D_52,'#skF_8')
      | ~ m1_subset_1(D_52,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_77,plain,(
    ! [D_52] :
      ( ~ v1_xboole_0('#skF_9')
      | ~ r2_hidden(D_52,'#skF_8')
      | ~ m1_subset_1(D_52,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_73,c_12])).

tff(c_147,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_36,plain,(
    ! [B_29,A_28] :
      ( r2_hidden(B_29,A_28)
      | ~ m1_subset_1(B_29,A_28)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_148,plain,(
    ! [D_69] :
      ( r2_hidden(D_69,'#skF_8')
      | ~ r2_hidden(D_69,'#skF_9')
      | ~ m1_subset_1(D_69,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_160,plain,(
    ! [B_29] :
      ( r2_hidden(B_29,'#skF_8')
      | ~ m1_subset_1(B_29,'#skF_7')
      | ~ m1_subset_1(B_29,'#skF_9')
      | v1_xboole_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_36,c_148])).

tff(c_399,plain,(
    ! [B_106] :
      ( r2_hidden(B_106,'#skF_8')
      | ~ m1_subset_1(B_106,'#skF_7')
      | ~ m1_subset_1(B_106,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_160])).

tff(c_424,plain,(
    ! [B_106] :
      ( ~ v1_xboole_0('#skF_8')
      | ~ m1_subset_1(B_106,'#skF_7')
      | ~ m1_subset_1(B_106,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_399,c_12])).

tff(c_425,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_424])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_58,plain,(
    ! [D_42] :
      ( r2_hidden(D_42,'#skF_9')
      | ~ r2_hidden(D_42,'#skF_8')
      | ~ m1_subset_1(D_42,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_113,plain,(
    ! [A_63,B_64] :
      ( ~ r2_hidden('#skF_1'(A_63,B_64),A_63)
      | ~ r2_xboole_0(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_587,plain,(
    ! [B_121] :
      ( ~ r2_xboole_0('#skF_9',B_121)
      | ~ r2_hidden('#skF_1'('#skF_9',B_121),'#skF_8')
      | ~ m1_subset_1('#skF_1'('#skF_9',B_121),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_58,c_113])).

tff(c_602,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_9','#skF_8'),'#skF_7')
    | ~ r2_xboole_0('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_10,c_587])).

tff(c_603,plain,(
    ~ r2_xboole_0('#skF_9','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_602])).

tff(c_606,plain,
    ( '#skF_9' = '#skF_8'
    | ~ r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_2,c_603])).

tff(c_609,plain,(
    ~ r1_tarski('#skF_9','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_606])).

tff(c_673,plain,(
    ! [A_134] :
      ( r2_hidden('#skF_1'(A_134,'#skF_9'),'#skF_8')
      | ~ m1_subset_1('#skF_1'(A_134,'#skF_9'),'#skF_7')
      | ~ r2_xboole_0(A_134,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_10,c_148])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),A_3)
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_699,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),'#skF_7')
    | ~ r2_xboole_0('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_673,c_8])).

tff(c_701,plain,(
    ~ r2_xboole_0('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_699])).

tff(c_704,plain,
    ( '#skF_9' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_2,c_701])).

tff(c_707,plain,(
    ~ r1_tarski('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_704])).

tff(c_46,plain,(
    ! [A_31,B_32,C_36] :
      ( r2_hidden('#skF_6'(A_31,B_32,C_36),B_32)
      | r1_tarski(B_32,C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(A_31))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3094,plain,(
    ! [A_215,B_216,C_217] :
      ( ~ r2_hidden('#skF_6'(A_215,B_216,C_217),C_217)
      | r1_tarski(B_216,C_217)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(A_215))
      | ~ m1_subset_1(B_216,k1_zfmisc_1(A_215)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_11403,plain,(
    ! [B_469,A_470] :
      ( r1_tarski(B_469,'#skF_9')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(A_470))
      | ~ m1_subset_1(B_469,k1_zfmisc_1(A_470))
      | ~ r2_hidden('#skF_6'(A_470,B_469,'#skF_9'),'#skF_8')
      | ~ m1_subset_1('#skF_6'(A_470,B_469,'#skF_9'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_58,c_3094])).

tff(c_11407,plain,(
    ! [A_31] :
      ( ~ m1_subset_1('#skF_6'(A_31,'#skF_8','#skF_9'),'#skF_7')
      | r1_tarski('#skF_8','#skF_9')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(A_31))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_31)) ) ),
    inference(resolution,[status(thm)],[c_46,c_11403])).

tff(c_21383,plain,(
    ! [A_575] :
      ( ~ m1_subset_1('#skF_6'(A_575,'#skF_8','#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(A_575))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_575)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_707,c_707,c_11407])).

tff(c_21387,plain,
    ( r1_tarski('#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_48,c_21383])).

tff(c_21393,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_21387])).

tff(c_21395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_707,c_21393])).

tff(c_21397,plain,(
    r2_xboole_0('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_699])).

tff(c_134,plain,(
    ! [B_67,A_68] :
      ( m1_subset_1(B_67,A_68)
      | ~ r2_hidden(B_67,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_145,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1('#skF_1'(A_3,B_4),B_4)
      | v1_xboole_0(B_4)
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_134])).

tff(c_38,plain,(
    ! [B_29,A_28] :
      ( m1_subset_1(B_29,A_28)
      | ~ v1_xboole_0(B_29)
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_21396,plain,(
    ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_699])).

tff(c_21414,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_8','#skF_9'))
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_21396])).

tff(c_21455,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_21414])).

tff(c_42,plain,(
    ! [A_30] : ~ v1_xboole_0(k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    ! [A_27] : k3_tarski(k1_zfmisc_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_163,plain,(
    ! [C_70,A_71,D_72] :
      ( r2_hidden(C_70,k3_tarski(A_71))
      | ~ r2_hidden(D_72,A_71)
      | ~ r2_hidden(C_70,D_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_21728,plain,(
    ! [C_612,A_613,B_614] :
      ( r2_hidden(C_612,k3_tarski(A_613))
      | ~ r2_hidden(C_612,B_614)
      | ~ m1_subset_1(B_614,A_613)
      | v1_xboole_0(A_613) ) ),
    inference(resolution,[status(thm)],[c_36,c_163])).

tff(c_28767,plain,(
    ! [B_814,A_815,A_816] :
      ( r2_hidden(B_814,k3_tarski(A_815))
      | ~ m1_subset_1(A_816,A_815)
      | v1_xboole_0(A_815)
      | ~ m1_subset_1(B_814,A_816)
      | v1_xboole_0(A_816) ) ),
    inference(resolution,[status(thm)],[c_36,c_21728])).

tff(c_28799,plain,(
    ! [B_814] :
      ( r2_hidden(B_814,k3_tarski(k1_zfmisc_1('#skF_7')))
      | v1_xboole_0(k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1(B_814,'#skF_9')
      | v1_xboole_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_52,c_28767])).

tff(c_28822,plain,(
    ! [B_814] :
      ( r2_hidden(B_814,'#skF_7')
      | v1_xboole_0(k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1(B_814,'#skF_9')
      | v1_xboole_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28799])).

tff(c_28905,plain,(
    ! [B_820] :
      ( r2_hidden(B_820,'#skF_7')
      | ~ m1_subset_1(B_820,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_42,c_28822])).

tff(c_34,plain,(
    ! [B_29,A_28] :
      ( m1_subset_1(B_29,A_28)
      | ~ r2_hidden(B_29,A_28)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28935,plain,(
    ! [B_820] :
      ( m1_subset_1(B_820,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(B_820,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_28905,c_34])).

tff(c_29011,plain,(
    ! [B_822] :
      ( m1_subset_1(B_822,'#skF_7')
      | ~ m1_subset_1(B_822,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_21455,c_28935])).

tff(c_29087,plain,(
    ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_29011,c_21396])).

tff(c_29230,plain,
    ( v1_xboole_0('#skF_9')
    | ~ r2_xboole_0('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_145,c_29087])).

tff(c_29236,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21397,c_29230])).

tff(c_29238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_29236])).

tff(c_29240,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_21414])).

tff(c_30145,plain,(
    ! [A_850,B_851,C_852] :
      ( m1_subset_1('#skF_6'(A_850,B_851,C_852),A_850)
      | r1_tarski(B_851,C_852)
      | ~ m1_subset_1(C_852,k1_zfmisc_1(A_850))
      | ~ m1_subset_1(B_851,k1_zfmisc_1(A_850)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_40,plain,(
    ! [B_29,A_28] :
      ( v1_xboole_0(B_29)
      | ~ m1_subset_1(B_29,A_28)
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_47202,plain,(
    ! [A_1083,B_1084,C_1085] :
      ( v1_xboole_0('#skF_6'(A_1083,B_1084,C_1085))
      | ~ v1_xboole_0(A_1083)
      | r1_tarski(B_1084,C_1085)
      | ~ m1_subset_1(C_1085,k1_zfmisc_1(A_1083))
      | ~ m1_subset_1(B_1084,k1_zfmisc_1(A_1083)) ) ),
    inference(resolution,[status(thm)],[c_30145,c_40])).

tff(c_47254,plain,(
    ! [B_1084] :
      ( v1_xboole_0('#skF_6'('#skF_7',B_1084,'#skF_8'))
      | ~ v1_xboole_0('#skF_7')
      | r1_tarski(B_1084,'#skF_8')
      | ~ m1_subset_1(B_1084,k1_zfmisc_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_54,c_47202])).

tff(c_47426,plain,(
    ! [B_1087] :
      ( v1_xboole_0('#skF_6'('#skF_7',B_1087,'#skF_8'))
      | r1_tarski(B_1087,'#skF_8')
      | ~ m1_subset_1(B_1087,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29240,c_47254])).

tff(c_47496,plain,
    ( v1_xboole_0('#skF_6'('#skF_7','#skF_9','#skF_8'))
    | r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_47426])).

tff(c_47546,plain,(
    v1_xboole_0('#skF_6'('#skF_7','#skF_9','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_609,c_47496])).

tff(c_451,plain,(
    ! [A_113,B_114] :
      ( r2_hidden('#skF_3'(A_113,B_114),A_113)
      | r2_hidden('#skF_4'(A_113,B_114),B_114)
      | k3_tarski(A_113) = B_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_611,plain,(
    ! [B_124,A_125] :
      ( ~ v1_xboole_0(B_124)
      | r2_hidden('#skF_3'(A_125,B_124),A_125)
      | k3_tarski(A_125) = B_124 ) ),
    inference(resolution,[status(thm)],[c_451,c_12])).

tff(c_657,plain,(
    ! [A_125,B_124] :
      ( ~ v1_xboole_0(A_125)
      | ~ v1_xboole_0(B_124)
      | k3_tarski(A_125) = B_124 ) ),
    inference(resolution,[status(thm)],[c_611,c_12])).

tff(c_29259,plain,(
    ! [B_824] :
      ( ~ v1_xboole_0(B_824)
      | k3_tarski('#skF_7') = B_824 ) ),
    inference(resolution,[status(thm)],[c_29240,c_657])).

tff(c_29263,plain,(
    k3_tarski('#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_29240,c_29259])).

tff(c_29255,plain,(
    ! [B_124] :
      ( ~ v1_xboole_0(B_124)
      | k3_tarski('#skF_7') = B_124 ) ),
    inference(resolution,[status(thm)],[c_29240,c_657])).

tff(c_29277,plain,(
    ! [B_124] :
      ( ~ v1_xboole_0(B_124)
      | B_124 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29263,c_29255])).

tff(c_47610,plain,(
    '#skF_6'('#skF_7','#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_47546,c_29277])).

tff(c_44,plain,(
    ! [A_31,B_32,C_36] :
      ( ~ r2_hidden('#skF_6'(A_31,B_32,C_36),C_36)
      | r1_tarski(B_32,C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(A_31))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_47668,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | r1_tarski('#skF_9','#skF_8')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_47610,c_44])).

tff(c_47681,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | r1_tarski('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_47668])).

tff(c_47682,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_609,c_47681])).

tff(c_47662,plain,
    ( m1_subset_1('#skF_7','#skF_7')
    | r1_tarski('#skF_9','#skF_8')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_47610,c_48])).

tff(c_47675,plain,
    ( m1_subset_1('#skF_7','#skF_7')
    | r1_tarski('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_47662])).

tff(c_47676,plain,(
    m1_subset_1('#skF_7','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_609,c_47675])).

tff(c_47665,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | r1_tarski('#skF_9','#skF_8')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_47610,c_46])).

tff(c_47678,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | r1_tarski('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_47665])).

tff(c_47679,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_609,c_47678])).

tff(c_56,plain,(
    ! [D_42] :
      ( r2_hidden(D_42,'#skF_8')
      | ~ r2_hidden(D_42,'#skF_9')
      | ~ m1_subset_1(D_42,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_47706,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_47679,c_56])).

tff(c_47718,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47676,c_47706])).

tff(c_47735,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47682,c_47718])).

tff(c_47737,plain,(
    r2_xboole_0('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_602])).

tff(c_47736,plain,(
    ~ m1_subset_1('#skF_1'('#skF_9','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_602])).

tff(c_47766,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_9','#skF_8'))
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_47736])).

tff(c_47795,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_47766])).

tff(c_48246,plain,(
    ! [C_1148,A_1149,B_1150] :
      ( r2_hidden(C_1148,k3_tarski(A_1149))
      | ~ r2_hidden(C_1148,B_1150)
      | ~ m1_subset_1(B_1150,A_1149)
      | v1_xboole_0(A_1149) ) ),
    inference(resolution,[status(thm)],[c_36,c_163])).

tff(c_53584,plain,(
    ! [B_1272,A_1273,A_1274] :
      ( r2_hidden(B_1272,k3_tarski(A_1273))
      | ~ m1_subset_1(A_1274,A_1273)
      | v1_xboole_0(A_1273)
      | ~ m1_subset_1(B_1272,A_1274)
      | v1_xboole_0(A_1274) ) ),
    inference(resolution,[status(thm)],[c_36,c_48246])).

tff(c_53612,plain,(
    ! [B_1272] :
      ( r2_hidden(B_1272,k3_tarski(k1_zfmisc_1('#skF_7')))
      | v1_xboole_0(k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1(B_1272,'#skF_8')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_54,c_53584])).

tff(c_53633,plain,(
    ! [B_1272] :
      ( r2_hidden(B_1272,'#skF_7')
      | v1_xboole_0(k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1(B_1272,'#skF_8')
      | v1_xboole_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_53612])).

tff(c_53688,plain,(
    ! [B_1276] :
      ( r2_hidden(B_1276,'#skF_7')
      | ~ m1_subset_1(B_1276,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_425,c_42,c_53633])).

tff(c_53718,plain,(
    ! [B_1276] :
      ( m1_subset_1(B_1276,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(B_1276,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_53688,c_34])).

tff(c_53882,plain,(
    ! [B_1281] :
      ( m1_subset_1(B_1281,'#skF_7')
      | ~ m1_subset_1(B_1281,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_47795,c_53718])).

tff(c_53942,plain,(
    ~ m1_subset_1('#skF_1'('#skF_9','#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_53882,c_47736])).

tff(c_54011,plain,
    ( v1_xboole_0('#skF_8')
    | ~ r2_xboole_0('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_145,c_53942])).

tff(c_54017,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47737,c_54011])).

tff(c_54019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_425,c_54017])).

tff(c_54021,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_47766])).

tff(c_538,plain,(
    ! [A_115,B_116] :
      ( ~ v1_xboole_0(A_115)
      | r2_hidden('#skF_4'(A_115,B_116),B_116)
      | k3_tarski(A_115) = B_116 ) ),
    inference(resolution,[status(thm)],[c_451,c_12])).

tff(c_584,plain,(
    ! [B_116,A_115] :
      ( ~ v1_xboole_0(B_116)
      | ~ v1_xboole_0(A_115)
      | k3_tarski(A_115) = B_116 ) ),
    inference(resolution,[status(thm)],[c_538,c_12])).

tff(c_54028,plain,(
    ! [A_1283] :
      ( ~ v1_xboole_0(A_1283)
      | k3_tarski(A_1283) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_54021,c_584])).

tff(c_54032,plain,(
    k3_tarski('#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_54021,c_54028])).

tff(c_16,plain,(
    ! [A_8,C_23] :
      ( r2_hidden('#skF_5'(A_8,k3_tarski(A_8),C_23),A_8)
      | ~ r2_hidden(C_23,k3_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_189,plain,(
    ! [A_77,C_78] :
      ( r2_hidden('#skF_5'(A_77,k3_tarski(A_77),C_78),A_77)
      | ~ r2_hidden(C_78,k3_tarski(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_226,plain,(
    ! [A_81,C_82] :
      ( ~ v1_xboole_0(A_81)
      | ~ r2_hidden(C_82,k3_tarski(A_81)) ) ),
    inference(resolution,[status(thm)],[c_189,c_12])).

tff(c_254,plain,(
    ! [A_85,C_86] :
      ( ~ v1_xboole_0(A_85)
      | ~ r2_hidden(C_86,k3_tarski(k3_tarski(A_85))) ) ),
    inference(resolution,[status(thm)],[c_16,c_226])).

tff(c_299,plain,(
    ! [A_90,C_91] :
      ( ~ v1_xboole_0(A_90)
      | ~ r2_hidden(C_91,k3_tarski(k3_tarski(k3_tarski(A_90)))) ) ),
    inference(resolution,[status(thm)],[c_16,c_254])).

tff(c_358,plain,(
    ! [A_100,C_101] :
      ( ~ v1_xboole_0(A_100)
      | ~ r2_hidden(C_101,k3_tarski(k3_tarski(k3_tarski(k3_tarski(A_100))))) ) ),
    inference(resolution,[status(thm)],[c_16,c_299])).

tff(c_374,plain,(
    ! [A_100,C_23] :
      ( ~ v1_xboole_0(A_100)
      | ~ r2_hidden(C_23,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(A_100)))))) ) ),
    inference(resolution,[status(thm)],[c_16,c_358])).

tff(c_54049,plain,(
    ! [C_23] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(C_23,k3_tarski(k3_tarski(k3_tarski(k3_tarski('#skF_7'))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54032,c_374])).

tff(c_54092,plain,(
    ! [C_23] : ~ r2_hidden(C_23,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54032,c_54032,c_54032,c_54032,c_54021,c_54049])).

tff(c_54154,plain,(
    ! [C_1289,D_1290] :
      ( r2_hidden(C_1289,k3_tarski('#skF_9'))
      | ~ r2_hidden(C_1289,D_1290)
      | ~ r2_hidden(D_1290,'#skF_8')
      | ~ m1_subset_1(D_1290,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_58,c_163])).

tff(c_54190,plain,(
    ! [D_42] :
      ( r2_hidden(D_42,k3_tarski('#skF_9'))
      | ~ r2_hidden('#skF_9','#skF_8')
      | ~ m1_subset_1('#skF_9','#skF_7')
      | ~ r2_hidden(D_42,'#skF_8')
      | ~ m1_subset_1(D_42,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_58,c_54154])).

tff(c_69862,plain,(
    ~ m1_subset_1('#skF_9','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_54190])).

tff(c_28,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_3'(A_8,B_9),A_8)
      | r2_hidden('#skF_4'(A_8,B_9),B_9)
      | k3_tarski(A_8) = B_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_54117,plain,(
    ! [C_1287] : ~ r2_hidden(C_1287,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54032,c_54032,c_54032,c_54032,c_54021,c_54049])).

tff(c_54125,plain,(
    ! [B_9] :
      ( r2_hidden('#skF_4'('#skF_7',B_9),B_9)
      | k3_tarski('#skF_7') = B_9 ) ),
    inference(resolution,[status(thm)],[c_28,c_54117])).

tff(c_54142,plain,(
    ! [B_9] :
      ( r2_hidden('#skF_4'('#skF_7',B_9),B_9)
      | B_9 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54032,c_54125])).

tff(c_54244,plain,(
    ! [B_1296] :
      ( r2_hidden('#skF_4'('#skF_7',B_1296),B_1296)
      | B_1296 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54032,c_54125])).

tff(c_14,plain,(
    ! [C_23,A_8,D_26] :
      ( r2_hidden(C_23,k3_tarski(A_8))
      | ~ r2_hidden(D_26,A_8)
      | ~ r2_hidden(C_23,D_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_71520,plain,(
    ! [C_1594,B_1595] :
      ( r2_hidden(C_1594,k3_tarski(B_1595))
      | ~ r2_hidden(C_1594,'#skF_4'('#skF_7',B_1595))
      | B_1595 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_54244,c_14])).

tff(c_71619,plain,(
    ! [B_1596,C_1597] :
      ( ~ v1_xboole_0(k3_tarski(B_1596))
      | ~ r2_hidden(C_1597,'#skF_4'('#skF_7',B_1596))
      | B_1596 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_71520,c_12])).

tff(c_71675,plain,(
    ! [B_1598] :
      ( ~ v1_xboole_0(k3_tarski(B_1598))
      | B_1598 = '#skF_7'
      | '#skF_4'('#skF_7',B_1598) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_54142,c_71619])).

tff(c_71716,plain,(
    ! [A_1601] :
      ( ~ v1_xboole_0(A_1601)
      | k1_zfmisc_1(A_1601) = '#skF_7'
      | '#skF_4'('#skF_7',k1_zfmisc_1(A_1601)) = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_71675])).

tff(c_529,plain,(
    ! [A_113,B_114] :
      ( ~ v1_xboole_0(A_113)
      | r2_hidden('#skF_4'(A_113,B_114),B_114)
      | k3_tarski(A_113) = B_114 ) ),
    inference(resolution,[status(thm)],[c_451,c_12])).

tff(c_71741,plain,(
    ! [A_1601] :
      ( ~ v1_xboole_0('#skF_7')
      | r2_hidden('#skF_7',k1_zfmisc_1(A_1601))
      | k3_tarski('#skF_7') = k1_zfmisc_1(A_1601)
      | ~ v1_xboole_0(A_1601)
      | k1_zfmisc_1(A_1601) = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71716,c_529])).

tff(c_71831,plain,(
    ! [A_1605] :
      ( r2_hidden('#skF_7',k1_zfmisc_1(A_1605))
      | ~ v1_xboole_0(A_1605)
      | k1_zfmisc_1(A_1605) = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54032,c_54021,c_71741])).

tff(c_71840,plain,(
    ! [A_1605] :
      ( m1_subset_1('#skF_7',k1_zfmisc_1(A_1605))
      | v1_xboole_0(k1_zfmisc_1(A_1605))
      | ~ v1_xboole_0(A_1605)
      | k1_zfmisc_1(A_1605) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_71831,c_34])).

tff(c_71852,plain,(
    ! [A_1606] :
      ( m1_subset_1('#skF_7',k1_zfmisc_1(A_1606))
      | ~ v1_xboole_0(A_1606)
      | k1_zfmisc_1(A_1606) = '#skF_7' ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_71840])).

tff(c_69538,plain,(
    ! [A_1526,B_1527,C_1528] :
      ( r2_hidden('#skF_6'(A_1526,B_1527,C_1528),B_1527)
      | r1_tarski(B_1527,C_1528)
      | ~ m1_subset_1(C_1528,k1_zfmisc_1(A_1526))
      | ~ m1_subset_1(B_1527,k1_zfmisc_1(A_1526)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_71483,plain,(
    ! [C_1592,A_1593] :
      ( r1_tarski('#skF_7',C_1592)
      | ~ m1_subset_1(C_1592,k1_zfmisc_1(A_1593))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_1593)) ) ),
    inference(resolution,[status(thm)],[c_69538,c_54092])).

tff(c_71511,plain,
    ( r1_tarski('#skF_7','#skF_9')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_52,c_71483])).

tff(c_71513,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_71511])).

tff(c_71855,plain,
    ( ~ v1_xboole_0('#skF_7')
    | k1_zfmisc_1('#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_71852,c_71513])).

tff(c_71865,plain,(
    k1_zfmisc_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54021,c_71855])).

tff(c_71871,plain,(
    m1_subset_1('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71865,c_52])).

tff(c_71874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69862,c_71871])).

tff(c_71876,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_71511])).

tff(c_69645,plain,(
    ! [A_1531,B_1532,C_1533] :
      ( m1_subset_1('#skF_6'(A_1531,B_1532,C_1533),A_1531)
      | r1_tarski(B_1532,C_1533)
      | ~ m1_subset_1(C_1533,k1_zfmisc_1(A_1531))
      | ~ m1_subset_1(B_1532,k1_zfmisc_1(A_1531)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_86677,plain,(
    ! [A_1773,B_1774,C_1775] :
      ( v1_xboole_0('#skF_6'(A_1773,B_1774,C_1775))
      | ~ v1_xboole_0(A_1773)
      | r1_tarski(B_1774,C_1775)
      | ~ m1_subset_1(C_1775,k1_zfmisc_1(A_1773))
      | ~ m1_subset_1(B_1774,k1_zfmisc_1(A_1773)) ) ),
    inference(resolution,[status(thm)],[c_69645,c_40])).

tff(c_86711,plain,(
    ! [B_1774] :
      ( v1_xboole_0('#skF_6'('#skF_7',B_1774,'#skF_7'))
      | ~ v1_xboole_0('#skF_7')
      | r1_tarski(B_1774,'#skF_7')
      | ~ m1_subset_1(B_1774,k1_zfmisc_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_71876,c_86677])).

tff(c_87023,plain,(
    ! [B_1778] :
      ( v1_xboole_0('#skF_6'('#skF_7',B_1778,'#skF_7'))
      | r1_tarski(B_1778,'#skF_7')
      | ~ m1_subset_1(B_1778,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54021,c_86711])).

tff(c_87141,plain,
    ( v1_xboole_0('#skF_6'('#skF_7','#skF_9','#skF_7'))
    | r1_tarski('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_87023])).

tff(c_87143,plain,(
    r1_tarski('#skF_9','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_87141])).

tff(c_245,plain,(
    ! [A_83,A_84] :
      ( ~ v1_xboole_0(A_83)
      | ~ r2_xboole_0(A_84,k3_tarski(A_83)) ) ),
    inference(resolution,[status(thm)],[c_10,c_226])).

tff(c_253,plain,(
    ! [A_83,A_1] :
      ( ~ v1_xboole_0(A_83)
      | k3_tarski(A_83) = A_1
      | ~ r1_tarski(A_1,k3_tarski(A_83)) ) ),
    inference(resolution,[status(thm)],[c_2,c_245])).

tff(c_54061,plain,(
    ! [A_1] :
      ( ~ v1_xboole_0('#skF_7')
      | k3_tarski('#skF_7') = A_1
      | ~ r1_tarski(A_1,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54032,c_253])).

tff(c_54099,plain,(
    ! [A_1] :
      ( A_1 = '#skF_7'
      | ~ r1_tarski(A_1,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54032,c_54021,c_54061])).

tff(c_87153,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_87143,c_54099])).

tff(c_87244,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87153,c_54021])).

tff(c_87259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_87244])).

tff(c_87261,plain,(
    ~ r1_tarski('#skF_9','#skF_7') ),
    inference(splitRight,[status(thm)],[c_87141])).

tff(c_87260,plain,(
    v1_xboole_0('#skF_6'('#skF_7','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_87141])).

tff(c_54304,plain,(
    ! [B_1296] :
      ( ~ v1_xboole_0(B_1296)
      | B_1296 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_54244,c_12])).

tff(c_87326,plain,(
    '#skF_6'('#skF_7','#skF_9','#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_87260,c_54304])).

tff(c_87341,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | r1_tarski('#skF_9','#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_87326,c_46])).

tff(c_87354,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | r1_tarski('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_71876,c_87341])).

tff(c_87355,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_87261,c_87354])).

tff(c_170,plain,(
    ! [C_70,A_28,B_29] :
      ( r2_hidden(C_70,k3_tarski(A_28))
      | ~ r2_hidden(C_70,B_29)
      | ~ m1_subset_1(B_29,A_28)
      | v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_36,c_163])).

tff(c_88061,plain,(
    ! [A_1794] :
      ( r2_hidden('#skF_7',k3_tarski(A_1794))
      | ~ m1_subset_1('#skF_9',A_1794)
      | v1_xboole_0(A_1794) ) ),
    inference(resolution,[status(thm)],[c_87355,c_170])).

tff(c_88180,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_7',A_27)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(A_27))
      | v1_xboole_0(k1_zfmisc_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_88061])).

tff(c_88208,plain,(
    ! [A_1795] :
      ( r2_hidden('#skF_7',A_1795)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(A_1795)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_88180])).

tff(c_88214,plain,(
    r2_hidden('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_88208])).

tff(c_88219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54092,c_88214])).

tff(c_88221,plain,(
    m1_subset_1('#skF_9','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54190])).

tff(c_88224,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_88221,c_40])).

tff(c_88227,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54021,c_88224])).

tff(c_88229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_88227])).

tff(c_88231,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_424])).

tff(c_88232,plain,(
    ! [A_1796,B_1797] :
      ( r2_hidden('#skF_3'(A_1796,B_1797),A_1796)
      | r2_hidden('#skF_4'(A_1796,B_1797),B_1797)
      | k3_tarski(A_1796) = B_1797 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_88347,plain,(
    ! [B_1803,A_1804] :
      ( ~ v1_xboole_0(B_1803)
      | r2_hidden('#skF_3'(A_1804,B_1803),A_1804)
      | k3_tarski(A_1804) = B_1803 ) ),
    inference(resolution,[status(thm)],[c_88232,c_12])).

tff(c_88392,plain,(
    ! [A_1805,B_1806] :
      ( ~ v1_xboole_0(A_1805)
      | ~ v1_xboole_0(B_1806)
      | k3_tarski(A_1805) = B_1806 ) ),
    inference(resolution,[status(thm)],[c_88347,c_12])).

tff(c_88396,plain,(
    ! [B_1807] :
      ( ~ v1_xboole_0(B_1807)
      | k3_tarski('#skF_8') = B_1807 ) ),
    inference(resolution,[status(thm)],[c_88231,c_88392])).

tff(c_88400,plain,(
    k3_tarski('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_88231,c_88396])).

tff(c_315,plain,(
    ! [A_90,C_23] :
      ( ~ v1_xboole_0(A_90)
      | ~ r2_hidden(C_23,k3_tarski(k3_tarski(k3_tarski(k3_tarski(A_90))))) ) ),
    inference(resolution,[status(thm)],[c_16,c_299])).

tff(c_88423,plain,(
    ! [C_23] :
      ( ~ v1_xboole_0('#skF_8')
      | ~ r2_hidden(C_23,k3_tarski(k3_tarski(k3_tarski('#skF_8')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88400,c_315])).

tff(c_88459,plain,(
    ! [C_23] : ~ r2_hidden(C_23,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88400,c_88400,c_88400,c_88231,c_88423])).

tff(c_88479,plain,(
    ! [D_42] :
      ( ~ r2_hidden(D_42,'#skF_9')
      | ~ m1_subset_1(D_42,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_88459,c_56])).

tff(c_102530,plain,(
    ! [A_2032,C_2033] :
      ( ~ m1_subset_1('#skF_6'(A_2032,'#skF_9',C_2033),'#skF_7')
      | r1_tarski('#skF_9',C_2033)
      | ~ m1_subset_1(C_2033,k1_zfmisc_1(A_2032))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(A_2032)) ) ),
    inference(resolution,[status(thm)],[c_89166,c_88479])).

tff(c_102534,plain,(
    ! [C_36] :
      ( r1_tarski('#skF_9',C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_48,c_102530])).

tff(c_102542,plain,(
    ! [C_2034] :
      ( r1_tarski('#skF_9',C_2034)
      | ~ m1_subset_1(C_2034,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_102534])).

tff(c_102641,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_102542])).

tff(c_88426,plain,(
    ! [A_1] :
      ( ~ v1_xboole_0('#skF_8')
      | k3_tarski('#skF_8') = A_1
      | ~ r1_tarski(A_1,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88400,c_253])).

tff(c_88461,plain,(
    ! [A_1] :
      ( A_1 = '#skF_8'
      | ~ r1_tarski(A_1,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88400,c_88231,c_88426])).

tff(c_102646,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_102641,c_88461])).

tff(c_102654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_102646])).

tff(c_102655,plain,(
    ! [D_52] :
      ( ~ r2_hidden(D_52,'#skF_8')
      | ~ m1_subset_1(D_52,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_124369,plain,(
    ! [A_2397,C_2398] :
      ( ~ m1_subset_1('#skF_6'(A_2397,'#skF_8',C_2398),'#skF_7')
      | r1_tarski('#skF_8',C_2398)
      | ~ m1_subset_1(C_2398,k1_zfmisc_1(A_2397))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_2397)) ) ),
    inference(resolution,[status(thm)],[c_104274,c_102655])).

tff(c_124373,plain,(
    ! [C_36] :
      ( r1_tarski('#skF_8',C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_48,c_124369])).

tff(c_124394,plain,(
    ! [C_2401] :
      ( r1_tarski('#skF_8',C_2401)
      | ~ m1_subset_1(C_2401,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_124373])).

tff(c_124505,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_124394])).

tff(c_102656,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_102818,plain,(
    ! [A_2059,B_2060] :
      ( r2_hidden('#skF_3'(A_2059,B_2060),A_2059)
      | r2_hidden('#skF_4'(A_2059,B_2060),B_2060)
      | k3_tarski(A_2059) = B_2060 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_103033,plain,(
    ! [A_2083,B_2084] :
      ( ~ v1_xboole_0(A_2083)
      | r2_hidden('#skF_4'(A_2083,B_2084),B_2084)
      | k3_tarski(A_2083) = B_2084 ) ),
    inference(resolution,[status(thm)],[c_102818,c_12])).

tff(c_103093,plain,(
    ! [B_2086,A_2087] :
      ( ~ v1_xboole_0(B_2086)
      | ~ v1_xboole_0(A_2087)
      | k3_tarski(A_2087) = B_2086 ) ),
    inference(resolution,[status(thm)],[c_103033,c_12])).

tff(c_103097,plain,(
    ! [A_2088] :
      ( ~ v1_xboole_0(A_2088)
      | k3_tarski(A_2088) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_102656,c_103093])).

tff(c_103101,plain,(
    k3_tarski('#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_102656,c_103097])).

tff(c_102792,plain,(
    ! [A_2057,C_2058] :
      ( r2_hidden('#skF_5'(A_2057,k3_tarski(A_2057),C_2058),A_2057)
      | ~ r2_hidden(C_2058,k3_tarski(A_2057)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_102855,plain,(
    ! [A_2061,C_2062] :
      ( ~ v1_xboole_0(A_2061)
      | ~ r2_hidden(C_2062,k3_tarski(A_2061)) ) ),
    inference(resolution,[status(thm)],[c_102792,c_12])).

tff(c_102884,plain,(
    ! [A_2063,A_2064] :
      ( ~ v1_xboole_0(A_2063)
      | ~ r2_xboole_0(A_2064,k3_tarski(A_2063)) ) ),
    inference(resolution,[status(thm)],[c_10,c_102855])).

tff(c_102892,plain,(
    ! [A_2063,A_1] :
      ( ~ v1_xboole_0(A_2063)
      | k3_tarski(A_2063) = A_1
      | ~ r1_tarski(A_1,k3_tarski(A_2063)) ) ),
    inference(resolution,[status(thm)],[c_2,c_102884])).

tff(c_103111,plain,(
    ! [A_1] :
      ( ~ v1_xboole_0('#skF_9')
      | k3_tarski('#skF_9') = A_1
      | ~ r1_tarski(A_1,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103101,c_102892])).

tff(c_103149,plain,(
    ! [A_1] :
      ( A_1 = '#skF_9'
      | ~ r1_tarski(A_1,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103101,c_102656,c_103111])).

tff(c_124514,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_124505,c_103149])).

tff(c_124523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_124514])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:25:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.54/15.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.65/15.55  
% 27.75/15.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.75/15.55  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 27.75/15.55  
% 27.75/15.55  %Foreground sorts:
% 27.75/15.55  
% 27.75/15.55  
% 27.75/15.55  %Background operators:
% 27.75/15.55  
% 27.75/15.55  
% 27.75/15.55  %Foreground operators:
% 27.75/15.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.75/15.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 27.75/15.55  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 27.75/15.55  tff('#skF_7', type, '#skF_7': $i).
% 27.75/15.55  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 27.75/15.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.75/15.55  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 27.75/15.55  tff('#skF_9', type, '#skF_9': $i).
% 27.75/15.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 27.75/15.55  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 27.75/15.55  tff('#skF_8', type, '#skF_8': $i).
% 27.75/15.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.75/15.55  tff(k3_tarski, type, k3_tarski: $i > $i).
% 27.75/15.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.75/15.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 27.75/15.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 27.75/15.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 27.75/15.55  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 27.75/15.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 27.75/15.55  
% 27.75/15.60  tff(f_104, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 27.75/15.60  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 27.75/15.60  tff(f_47, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 27.75/15.60  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 27.75/15.60  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 27.75/15.60  tff(f_42, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 27.75/15.60  tff(f_75, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 27.75/15.60  tff(f_59, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 27.75/15.60  tff(f_57, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 27.75/15.60  tff(c_50, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_104])).
% 27.75/15.60  tff(c_52, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 27.75/15.60  tff(c_54, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 27.75/15.60  tff(c_48, plain, (![A_31, B_32, C_36]: (m1_subset_1('#skF_6'(A_31, B_32, C_36), A_31) | r1_tarski(B_32, C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(A_31)) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 27.75/15.60  tff(c_104274, plain, (![A_2131, B_2132, C_2133]: (r2_hidden('#skF_6'(A_2131, B_2132, C_2133), B_2132) | r1_tarski(B_2132, C_2133) | ~m1_subset_1(C_2133, k1_zfmisc_1(A_2131)) | ~m1_subset_1(B_2132, k1_zfmisc_1(A_2131)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 27.75/15.60  tff(c_89166, plain, (![A_1844, B_1845, C_1846]: (r2_hidden('#skF_6'(A_1844, B_1845, C_1846), B_1845) | r1_tarski(B_1845, C_1846) | ~m1_subset_1(C_1846, k1_zfmisc_1(A_1844)) | ~m1_subset_1(B_1845, k1_zfmisc_1(A_1844)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 27.75/15.60  tff(c_73, plain, (![D_52]: (r2_hidden(D_52, '#skF_9') | ~r2_hidden(D_52, '#skF_8') | ~m1_subset_1(D_52, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 27.75/15.60  tff(c_12, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 27.75/15.60  tff(c_77, plain, (![D_52]: (~v1_xboole_0('#skF_9') | ~r2_hidden(D_52, '#skF_8') | ~m1_subset_1(D_52, '#skF_7'))), inference(resolution, [status(thm)], [c_73, c_12])).
% 27.75/15.60  tff(c_147, plain, (~v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_77])).
% 27.75/15.60  tff(c_36, plain, (![B_29, A_28]: (r2_hidden(B_29, A_28) | ~m1_subset_1(B_29, A_28) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_72])).
% 27.75/15.60  tff(c_148, plain, (![D_69]: (r2_hidden(D_69, '#skF_8') | ~r2_hidden(D_69, '#skF_9') | ~m1_subset_1(D_69, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 27.75/15.60  tff(c_160, plain, (![B_29]: (r2_hidden(B_29, '#skF_8') | ~m1_subset_1(B_29, '#skF_7') | ~m1_subset_1(B_29, '#skF_9') | v1_xboole_0('#skF_9'))), inference(resolution, [status(thm)], [c_36, c_148])).
% 27.75/15.60  tff(c_399, plain, (![B_106]: (r2_hidden(B_106, '#skF_8') | ~m1_subset_1(B_106, '#skF_7') | ~m1_subset_1(B_106, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_147, c_160])).
% 27.75/15.60  tff(c_424, plain, (![B_106]: (~v1_xboole_0('#skF_8') | ~m1_subset_1(B_106, '#skF_7') | ~m1_subset_1(B_106, '#skF_9'))), inference(resolution, [status(thm)], [c_399, c_12])).
% 27.75/15.60  tff(c_425, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_424])).
% 27.75/15.60  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 27.75/15.60  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 27.75/15.60  tff(c_58, plain, (![D_42]: (r2_hidden(D_42, '#skF_9') | ~r2_hidden(D_42, '#skF_8') | ~m1_subset_1(D_42, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 27.75/15.60  tff(c_113, plain, (![A_63, B_64]: (~r2_hidden('#skF_1'(A_63, B_64), A_63) | ~r2_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_42])).
% 27.75/15.60  tff(c_587, plain, (![B_121]: (~r2_xboole_0('#skF_9', B_121) | ~r2_hidden('#skF_1'('#skF_9', B_121), '#skF_8') | ~m1_subset_1('#skF_1'('#skF_9', B_121), '#skF_7'))), inference(resolution, [status(thm)], [c_58, c_113])).
% 27.75/15.60  tff(c_602, plain, (~m1_subset_1('#skF_1'('#skF_9', '#skF_8'), '#skF_7') | ~r2_xboole_0('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_10, c_587])).
% 27.75/15.60  tff(c_603, plain, (~r2_xboole_0('#skF_9', '#skF_8')), inference(splitLeft, [status(thm)], [c_602])).
% 27.75/15.60  tff(c_606, plain, ('#skF_9'='#skF_8' | ~r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_2, c_603])).
% 27.75/15.60  tff(c_609, plain, (~r1_tarski('#skF_9', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_50, c_606])).
% 27.75/15.60  tff(c_673, plain, (![A_134]: (r2_hidden('#skF_1'(A_134, '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_1'(A_134, '#skF_9'), '#skF_7') | ~r2_xboole_0(A_134, '#skF_9'))), inference(resolution, [status(thm)], [c_10, c_148])).
% 27.75/15.60  tff(c_8, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), A_3) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 27.75/15.60  tff(c_699, plain, (~m1_subset_1('#skF_1'('#skF_8', '#skF_9'), '#skF_7') | ~r2_xboole_0('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_673, c_8])).
% 27.75/15.60  tff(c_701, plain, (~r2_xboole_0('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_699])).
% 27.75/15.60  tff(c_704, plain, ('#skF_9'='#skF_8' | ~r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_2, c_701])).
% 27.75/15.60  tff(c_707, plain, (~r1_tarski('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_50, c_704])).
% 27.75/15.60  tff(c_46, plain, (![A_31, B_32, C_36]: (r2_hidden('#skF_6'(A_31, B_32, C_36), B_32) | r1_tarski(B_32, C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(A_31)) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 27.75/15.60  tff(c_3094, plain, (![A_215, B_216, C_217]: (~r2_hidden('#skF_6'(A_215, B_216, C_217), C_217) | r1_tarski(B_216, C_217) | ~m1_subset_1(C_217, k1_zfmisc_1(A_215)) | ~m1_subset_1(B_216, k1_zfmisc_1(A_215)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 27.75/15.60  tff(c_11403, plain, (![B_469, A_470]: (r1_tarski(B_469, '#skF_9') | ~m1_subset_1('#skF_9', k1_zfmisc_1(A_470)) | ~m1_subset_1(B_469, k1_zfmisc_1(A_470)) | ~r2_hidden('#skF_6'(A_470, B_469, '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'(A_470, B_469, '#skF_9'), '#skF_7'))), inference(resolution, [status(thm)], [c_58, c_3094])).
% 27.75/15.60  tff(c_11407, plain, (![A_31]: (~m1_subset_1('#skF_6'(A_31, '#skF_8', '#skF_9'), '#skF_7') | r1_tarski('#skF_8', '#skF_9') | ~m1_subset_1('#skF_9', k1_zfmisc_1(A_31)) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_31)))), inference(resolution, [status(thm)], [c_46, c_11403])).
% 27.75/15.60  tff(c_21383, plain, (![A_575]: (~m1_subset_1('#skF_6'(A_575, '#skF_8', '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(A_575)) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_575)))), inference(negUnitSimplification, [status(thm)], [c_707, c_707, c_11407])).
% 27.75/15.60  tff(c_21387, plain, (r1_tarski('#skF_8', '#skF_9') | ~m1_subset_1('#skF_9', k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_48, c_21383])).
% 27.75/15.60  tff(c_21393, plain, (r1_tarski('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_21387])).
% 27.75/15.60  tff(c_21395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_707, c_21393])).
% 27.75/15.60  tff(c_21397, plain, (r2_xboole_0('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_699])).
% 27.75/15.60  tff(c_134, plain, (![B_67, A_68]: (m1_subset_1(B_67, A_68) | ~r2_hidden(B_67, A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_72])).
% 27.75/15.60  tff(c_145, plain, (![A_3, B_4]: (m1_subset_1('#skF_1'(A_3, B_4), B_4) | v1_xboole_0(B_4) | ~r2_xboole_0(A_3, B_4))), inference(resolution, [status(thm)], [c_10, c_134])).
% 27.75/15.60  tff(c_38, plain, (![B_29, A_28]: (m1_subset_1(B_29, A_28) | ~v1_xboole_0(B_29) | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_72])).
% 27.75/15.60  tff(c_21396, plain, (~m1_subset_1('#skF_1'('#skF_8', '#skF_9'), '#skF_7')), inference(splitRight, [status(thm)], [c_699])).
% 27.75/15.60  tff(c_21414, plain, (~v1_xboole_0('#skF_1'('#skF_8', '#skF_9')) | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_38, c_21396])).
% 27.75/15.60  tff(c_21455, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_21414])).
% 27.75/15.60  tff(c_42, plain, (![A_30]: (~v1_xboole_0(k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 27.75/15.60  tff(c_32, plain, (![A_27]: (k3_tarski(k1_zfmisc_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_59])).
% 27.75/15.60  tff(c_163, plain, (![C_70, A_71, D_72]: (r2_hidden(C_70, k3_tarski(A_71)) | ~r2_hidden(D_72, A_71) | ~r2_hidden(C_70, D_72))), inference(cnfTransformation, [status(thm)], [f_57])).
% 27.75/15.60  tff(c_21728, plain, (![C_612, A_613, B_614]: (r2_hidden(C_612, k3_tarski(A_613)) | ~r2_hidden(C_612, B_614) | ~m1_subset_1(B_614, A_613) | v1_xboole_0(A_613))), inference(resolution, [status(thm)], [c_36, c_163])).
% 27.75/15.60  tff(c_28767, plain, (![B_814, A_815, A_816]: (r2_hidden(B_814, k3_tarski(A_815)) | ~m1_subset_1(A_816, A_815) | v1_xboole_0(A_815) | ~m1_subset_1(B_814, A_816) | v1_xboole_0(A_816))), inference(resolution, [status(thm)], [c_36, c_21728])).
% 27.75/15.60  tff(c_28799, plain, (![B_814]: (r2_hidden(B_814, k3_tarski(k1_zfmisc_1('#skF_7'))) | v1_xboole_0(k1_zfmisc_1('#skF_7')) | ~m1_subset_1(B_814, '#skF_9') | v1_xboole_0('#skF_9'))), inference(resolution, [status(thm)], [c_52, c_28767])).
% 27.75/15.60  tff(c_28822, plain, (![B_814]: (r2_hidden(B_814, '#skF_7') | v1_xboole_0(k1_zfmisc_1('#skF_7')) | ~m1_subset_1(B_814, '#skF_9') | v1_xboole_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28799])).
% 27.75/15.60  tff(c_28905, plain, (![B_820]: (r2_hidden(B_820, '#skF_7') | ~m1_subset_1(B_820, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_147, c_42, c_28822])).
% 27.75/15.60  tff(c_34, plain, (![B_29, A_28]: (m1_subset_1(B_29, A_28) | ~r2_hidden(B_29, A_28) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_72])).
% 27.75/15.60  tff(c_28935, plain, (![B_820]: (m1_subset_1(B_820, '#skF_7') | v1_xboole_0('#skF_7') | ~m1_subset_1(B_820, '#skF_9'))), inference(resolution, [status(thm)], [c_28905, c_34])).
% 27.75/15.60  tff(c_29011, plain, (![B_822]: (m1_subset_1(B_822, '#skF_7') | ~m1_subset_1(B_822, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_21455, c_28935])).
% 27.75/15.60  tff(c_29087, plain, (~m1_subset_1('#skF_1'('#skF_8', '#skF_9'), '#skF_9')), inference(resolution, [status(thm)], [c_29011, c_21396])).
% 27.75/15.60  tff(c_29230, plain, (v1_xboole_0('#skF_9') | ~r2_xboole_0('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_145, c_29087])).
% 27.75/15.60  tff(c_29236, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_21397, c_29230])).
% 27.75/15.60  tff(c_29238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_29236])).
% 27.75/15.60  tff(c_29240, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_21414])).
% 27.75/15.60  tff(c_30145, plain, (![A_850, B_851, C_852]: (m1_subset_1('#skF_6'(A_850, B_851, C_852), A_850) | r1_tarski(B_851, C_852) | ~m1_subset_1(C_852, k1_zfmisc_1(A_850)) | ~m1_subset_1(B_851, k1_zfmisc_1(A_850)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 27.75/15.60  tff(c_40, plain, (![B_29, A_28]: (v1_xboole_0(B_29) | ~m1_subset_1(B_29, A_28) | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_72])).
% 27.75/15.60  tff(c_47202, plain, (![A_1083, B_1084, C_1085]: (v1_xboole_0('#skF_6'(A_1083, B_1084, C_1085)) | ~v1_xboole_0(A_1083) | r1_tarski(B_1084, C_1085) | ~m1_subset_1(C_1085, k1_zfmisc_1(A_1083)) | ~m1_subset_1(B_1084, k1_zfmisc_1(A_1083)))), inference(resolution, [status(thm)], [c_30145, c_40])).
% 27.75/15.60  tff(c_47254, plain, (![B_1084]: (v1_xboole_0('#skF_6'('#skF_7', B_1084, '#skF_8')) | ~v1_xboole_0('#skF_7') | r1_tarski(B_1084, '#skF_8') | ~m1_subset_1(B_1084, k1_zfmisc_1('#skF_7')))), inference(resolution, [status(thm)], [c_54, c_47202])).
% 27.75/15.60  tff(c_47426, plain, (![B_1087]: (v1_xboole_0('#skF_6'('#skF_7', B_1087, '#skF_8')) | r1_tarski(B_1087, '#skF_8') | ~m1_subset_1(B_1087, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_29240, c_47254])).
% 27.75/15.60  tff(c_47496, plain, (v1_xboole_0('#skF_6'('#skF_7', '#skF_9', '#skF_8')) | r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_52, c_47426])).
% 27.75/15.60  tff(c_47546, plain, (v1_xboole_0('#skF_6'('#skF_7', '#skF_9', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_609, c_47496])).
% 27.75/15.60  tff(c_451, plain, (![A_113, B_114]: (r2_hidden('#skF_3'(A_113, B_114), A_113) | r2_hidden('#skF_4'(A_113, B_114), B_114) | k3_tarski(A_113)=B_114)), inference(cnfTransformation, [status(thm)], [f_57])).
% 27.75/15.60  tff(c_611, plain, (![B_124, A_125]: (~v1_xboole_0(B_124) | r2_hidden('#skF_3'(A_125, B_124), A_125) | k3_tarski(A_125)=B_124)), inference(resolution, [status(thm)], [c_451, c_12])).
% 27.75/15.60  tff(c_657, plain, (![A_125, B_124]: (~v1_xboole_0(A_125) | ~v1_xboole_0(B_124) | k3_tarski(A_125)=B_124)), inference(resolution, [status(thm)], [c_611, c_12])).
% 27.75/15.60  tff(c_29259, plain, (![B_824]: (~v1_xboole_0(B_824) | k3_tarski('#skF_7')=B_824)), inference(resolution, [status(thm)], [c_29240, c_657])).
% 27.75/15.60  tff(c_29263, plain, (k3_tarski('#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_29240, c_29259])).
% 27.75/15.60  tff(c_29255, plain, (![B_124]: (~v1_xboole_0(B_124) | k3_tarski('#skF_7')=B_124)), inference(resolution, [status(thm)], [c_29240, c_657])).
% 27.75/15.60  tff(c_29277, plain, (![B_124]: (~v1_xboole_0(B_124) | B_124='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_29263, c_29255])).
% 27.75/15.60  tff(c_47610, plain, ('#skF_6'('#skF_7', '#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_47546, c_29277])).
% 27.75/15.60  tff(c_44, plain, (![A_31, B_32, C_36]: (~r2_hidden('#skF_6'(A_31, B_32, C_36), C_36) | r1_tarski(B_32, C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(A_31)) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 27.75/15.60  tff(c_47668, plain, (~r2_hidden('#skF_7', '#skF_8') | r1_tarski('#skF_9', '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_47610, c_44])).
% 27.75/15.60  tff(c_47681, plain, (~r2_hidden('#skF_7', '#skF_8') | r1_tarski('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_47668])).
% 27.75/15.60  tff(c_47682, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_609, c_47681])).
% 27.75/15.60  tff(c_47662, plain, (m1_subset_1('#skF_7', '#skF_7') | r1_tarski('#skF_9', '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_47610, c_48])).
% 27.75/15.60  tff(c_47675, plain, (m1_subset_1('#skF_7', '#skF_7') | r1_tarski('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_47662])).
% 27.75/15.60  tff(c_47676, plain, (m1_subset_1('#skF_7', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_609, c_47675])).
% 27.75/15.60  tff(c_47665, plain, (r2_hidden('#skF_7', '#skF_9') | r1_tarski('#skF_9', '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_47610, c_46])).
% 27.75/15.60  tff(c_47678, plain, (r2_hidden('#skF_7', '#skF_9') | r1_tarski('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_47665])).
% 27.75/15.60  tff(c_47679, plain, (r2_hidden('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_609, c_47678])).
% 27.75/15.60  tff(c_56, plain, (![D_42]: (r2_hidden(D_42, '#skF_8') | ~r2_hidden(D_42, '#skF_9') | ~m1_subset_1(D_42, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 27.75/15.60  tff(c_47706, plain, (r2_hidden('#skF_7', '#skF_8') | ~m1_subset_1('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_47679, c_56])).
% 27.75/15.60  tff(c_47718, plain, (r2_hidden('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_47676, c_47706])).
% 27.75/15.60  tff(c_47735, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47682, c_47718])).
% 27.75/15.60  tff(c_47737, plain, (r2_xboole_0('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_602])).
% 27.75/15.60  tff(c_47736, plain, (~m1_subset_1('#skF_1'('#skF_9', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_602])).
% 27.75/15.60  tff(c_47766, plain, (~v1_xboole_0('#skF_1'('#skF_9', '#skF_8')) | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_38, c_47736])).
% 27.75/15.60  tff(c_47795, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_47766])).
% 27.75/15.60  tff(c_48246, plain, (![C_1148, A_1149, B_1150]: (r2_hidden(C_1148, k3_tarski(A_1149)) | ~r2_hidden(C_1148, B_1150) | ~m1_subset_1(B_1150, A_1149) | v1_xboole_0(A_1149))), inference(resolution, [status(thm)], [c_36, c_163])).
% 27.75/15.60  tff(c_53584, plain, (![B_1272, A_1273, A_1274]: (r2_hidden(B_1272, k3_tarski(A_1273)) | ~m1_subset_1(A_1274, A_1273) | v1_xboole_0(A_1273) | ~m1_subset_1(B_1272, A_1274) | v1_xboole_0(A_1274))), inference(resolution, [status(thm)], [c_36, c_48246])).
% 27.75/15.60  tff(c_53612, plain, (![B_1272]: (r2_hidden(B_1272, k3_tarski(k1_zfmisc_1('#skF_7'))) | v1_xboole_0(k1_zfmisc_1('#skF_7')) | ~m1_subset_1(B_1272, '#skF_8') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_54, c_53584])).
% 27.75/15.60  tff(c_53633, plain, (![B_1272]: (r2_hidden(B_1272, '#skF_7') | v1_xboole_0(k1_zfmisc_1('#skF_7')) | ~m1_subset_1(B_1272, '#skF_8') | v1_xboole_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_53612])).
% 27.75/15.60  tff(c_53688, plain, (![B_1276]: (r2_hidden(B_1276, '#skF_7') | ~m1_subset_1(B_1276, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_425, c_42, c_53633])).
% 27.75/15.60  tff(c_53718, plain, (![B_1276]: (m1_subset_1(B_1276, '#skF_7') | v1_xboole_0('#skF_7') | ~m1_subset_1(B_1276, '#skF_8'))), inference(resolution, [status(thm)], [c_53688, c_34])).
% 27.75/15.60  tff(c_53882, plain, (![B_1281]: (m1_subset_1(B_1281, '#skF_7') | ~m1_subset_1(B_1281, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_47795, c_53718])).
% 27.75/15.60  tff(c_53942, plain, (~m1_subset_1('#skF_1'('#skF_9', '#skF_8'), '#skF_8')), inference(resolution, [status(thm)], [c_53882, c_47736])).
% 27.75/15.60  tff(c_54011, plain, (v1_xboole_0('#skF_8') | ~r2_xboole_0('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_145, c_53942])).
% 27.75/15.60  tff(c_54017, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_47737, c_54011])).
% 27.75/15.60  tff(c_54019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_425, c_54017])).
% 27.75/15.60  tff(c_54021, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_47766])).
% 27.75/15.60  tff(c_538, plain, (![A_115, B_116]: (~v1_xboole_0(A_115) | r2_hidden('#skF_4'(A_115, B_116), B_116) | k3_tarski(A_115)=B_116)), inference(resolution, [status(thm)], [c_451, c_12])).
% 27.75/15.60  tff(c_584, plain, (![B_116, A_115]: (~v1_xboole_0(B_116) | ~v1_xboole_0(A_115) | k3_tarski(A_115)=B_116)), inference(resolution, [status(thm)], [c_538, c_12])).
% 27.75/15.60  tff(c_54028, plain, (![A_1283]: (~v1_xboole_0(A_1283) | k3_tarski(A_1283)='#skF_7')), inference(resolution, [status(thm)], [c_54021, c_584])).
% 27.75/15.60  tff(c_54032, plain, (k3_tarski('#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_54021, c_54028])).
% 27.75/15.60  tff(c_16, plain, (![A_8, C_23]: (r2_hidden('#skF_5'(A_8, k3_tarski(A_8), C_23), A_8) | ~r2_hidden(C_23, k3_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 27.75/15.60  tff(c_189, plain, (![A_77, C_78]: (r2_hidden('#skF_5'(A_77, k3_tarski(A_77), C_78), A_77) | ~r2_hidden(C_78, k3_tarski(A_77)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 27.75/15.60  tff(c_226, plain, (![A_81, C_82]: (~v1_xboole_0(A_81) | ~r2_hidden(C_82, k3_tarski(A_81)))), inference(resolution, [status(thm)], [c_189, c_12])).
% 27.75/15.60  tff(c_254, plain, (![A_85, C_86]: (~v1_xboole_0(A_85) | ~r2_hidden(C_86, k3_tarski(k3_tarski(A_85))))), inference(resolution, [status(thm)], [c_16, c_226])).
% 27.75/15.60  tff(c_299, plain, (![A_90, C_91]: (~v1_xboole_0(A_90) | ~r2_hidden(C_91, k3_tarski(k3_tarski(k3_tarski(A_90)))))), inference(resolution, [status(thm)], [c_16, c_254])).
% 27.75/15.60  tff(c_358, plain, (![A_100, C_101]: (~v1_xboole_0(A_100) | ~r2_hidden(C_101, k3_tarski(k3_tarski(k3_tarski(k3_tarski(A_100))))))), inference(resolution, [status(thm)], [c_16, c_299])).
% 27.75/15.60  tff(c_374, plain, (![A_100, C_23]: (~v1_xboole_0(A_100) | ~r2_hidden(C_23, k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(A_100)))))))), inference(resolution, [status(thm)], [c_16, c_358])).
% 27.75/15.60  tff(c_54049, plain, (![C_23]: (~v1_xboole_0('#skF_7') | ~r2_hidden(C_23, k3_tarski(k3_tarski(k3_tarski(k3_tarski('#skF_7'))))))), inference(superposition, [status(thm), theory('equality')], [c_54032, c_374])).
% 27.75/15.60  tff(c_54092, plain, (![C_23]: (~r2_hidden(C_23, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_54032, c_54032, c_54032, c_54032, c_54021, c_54049])).
% 27.75/15.60  tff(c_54154, plain, (![C_1289, D_1290]: (r2_hidden(C_1289, k3_tarski('#skF_9')) | ~r2_hidden(C_1289, D_1290) | ~r2_hidden(D_1290, '#skF_8') | ~m1_subset_1(D_1290, '#skF_7'))), inference(resolution, [status(thm)], [c_58, c_163])).
% 27.75/15.60  tff(c_54190, plain, (![D_42]: (r2_hidden(D_42, k3_tarski('#skF_9')) | ~r2_hidden('#skF_9', '#skF_8') | ~m1_subset_1('#skF_9', '#skF_7') | ~r2_hidden(D_42, '#skF_8') | ~m1_subset_1(D_42, '#skF_7'))), inference(resolution, [status(thm)], [c_58, c_54154])).
% 27.75/15.60  tff(c_69862, plain, (~m1_subset_1('#skF_9', '#skF_7')), inference(splitLeft, [status(thm)], [c_54190])).
% 27.75/15.60  tff(c_28, plain, (![A_8, B_9]: (r2_hidden('#skF_3'(A_8, B_9), A_8) | r2_hidden('#skF_4'(A_8, B_9), B_9) | k3_tarski(A_8)=B_9)), inference(cnfTransformation, [status(thm)], [f_57])).
% 27.75/15.60  tff(c_54117, plain, (![C_1287]: (~r2_hidden(C_1287, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_54032, c_54032, c_54032, c_54032, c_54021, c_54049])).
% 27.75/15.60  tff(c_54125, plain, (![B_9]: (r2_hidden('#skF_4'('#skF_7', B_9), B_9) | k3_tarski('#skF_7')=B_9)), inference(resolution, [status(thm)], [c_28, c_54117])).
% 27.75/15.60  tff(c_54142, plain, (![B_9]: (r2_hidden('#skF_4'('#skF_7', B_9), B_9) | B_9='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_54032, c_54125])).
% 27.75/15.60  tff(c_54244, plain, (![B_1296]: (r2_hidden('#skF_4'('#skF_7', B_1296), B_1296) | B_1296='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_54032, c_54125])).
% 27.75/15.60  tff(c_14, plain, (![C_23, A_8, D_26]: (r2_hidden(C_23, k3_tarski(A_8)) | ~r2_hidden(D_26, A_8) | ~r2_hidden(C_23, D_26))), inference(cnfTransformation, [status(thm)], [f_57])).
% 27.75/15.60  tff(c_71520, plain, (![C_1594, B_1595]: (r2_hidden(C_1594, k3_tarski(B_1595)) | ~r2_hidden(C_1594, '#skF_4'('#skF_7', B_1595)) | B_1595='#skF_7')), inference(resolution, [status(thm)], [c_54244, c_14])).
% 27.75/15.60  tff(c_71619, plain, (![B_1596, C_1597]: (~v1_xboole_0(k3_tarski(B_1596)) | ~r2_hidden(C_1597, '#skF_4'('#skF_7', B_1596)) | B_1596='#skF_7')), inference(resolution, [status(thm)], [c_71520, c_12])).
% 27.75/15.60  tff(c_71675, plain, (![B_1598]: (~v1_xboole_0(k3_tarski(B_1598)) | B_1598='#skF_7' | '#skF_4'('#skF_7', B_1598)='#skF_7')), inference(resolution, [status(thm)], [c_54142, c_71619])).
% 27.75/15.60  tff(c_71716, plain, (![A_1601]: (~v1_xboole_0(A_1601) | k1_zfmisc_1(A_1601)='#skF_7' | '#skF_4'('#skF_7', k1_zfmisc_1(A_1601))='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_32, c_71675])).
% 27.75/15.60  tff(c_529, plain, (![A_113, B_114]: (~v1_xboole_0(A_113) | r2_hidden('#skF_4'(A_113, B_114), B_114) | k3_tarski(A_113)=B_114)), inference(resolution, [status(thm)], [c_451, c_12])).
% 27.75/15.60  tff(c_71741, plain, (![A_1601]: (~v1_xboole_0('#skF_7') | r2_hidden('#skF_7', k1_zfmisc_1(A_1601)) | k3_tarski('#skF_7')=k1_zfmisc_1(A_1601) | ~v1_xboole_0(A_1601) | k1_zfmisc_1(A_1601)='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_71716, c_529])).
% 27.75/15.60  tff(c_71831, plain, (![A_1605]: (r2_hidden('#skF_7', k1_zfmisc_1(A_1605)) | ~v1_xboole_0(A_1605) | k1_zfmisc_1(A_1605)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_54032, c_54021, c_71741])).
% 27.75/15.60  tff(c_71840, plain, (![A_1605]: (m1_subset_1('#skF_7', k1_zfmisc_1(A_1605)) | v1_xboole_0(k1_zfmisc_1(A_1605)) | ~v1_xboole_0(A_1605) | k1_zfmisc_1(A_1605)='#skF_7')), inference(resolution, [status(thm)], [c_71831, c_34])).
% 27.75/15.60  tff(c_71852, plain, (![A_1606]: (m1_subset_1('#skF_7', k1_zfmisc_1(A_1606)) | ~v1_xboole_0(A_1606) | k1_zfmisc_1(A_1606)='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_42, c_71840])).
% 27.75/15.60  tff(c_69538, plain, (![A_1526, B_1527, C_1528]: (r2_hidden('#skF_6'(A_1526, B_1527, C_1528), B_1527) | r1_tarski(B_1527, C_1528) | ~m1_subset_1(C_1528, k1_zfmisc_1(A_1526)) | ~m1_subset_1(B_1527, k1_zfmisc_1(A_1526)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 27.75/15.60  tff(c_71483, plain, (![C_1592, A_1593]: (r1_tarski('#skF_7', C_1592) | ~m1_subset_1(C_1592, k1_zfmisc_1(A_1593)) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_1593)))), inference(resolution, [status(thm)], [c_69538, c_54092])).
% 27.75/15.60  tff(c_71511, plain, (r1_tarski('#skF_7', '#skF_9') | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_52, c_71483])).
% 27.75/15.60  tff(c_71513, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_71511])).
% 27.75/15.60  tff(c_71855, plain, (~v1_xboole_0('#skF_7') | k1_zfmisc_1('#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_71852, c_71513])).
% 27.75/15.60  tff(c_71865, plain, (k1_zfmisc_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_54021, c_71855])).
% 27.75/15.60  tff(c_71871, plain, (m1_subset_1('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_71865, c_52])).
% 27.75/15.60  tff(c_71874, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69862, c_71871])).
% 27.75/15.60  tff(c_71876, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(splitRight, [status(thm)], [c_71511])).
% 27.75/15.60  tff(c_69645, plain, (![A_1531, B_1532, C_1533]: (m1_subset_1('#skF_6'(A_1531, B_1532, C_1533), A_1531) | r1_tarski(B_1532, C_1533) | ~m1_subset_1(C_1533, k1_zfmisc_1(A_1531)) | ~m1_subset_1(B_1532, k1_zfmisc_1(A_1531)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 27.75/15.60  tff(c_86677, plain, (![A_1773, B_1774, C_1775]: (v1_xboole_0('#skF_6'(A_1773, B_1774, C_1775)) | ~v1_xboole_0(A_1773) | r1_tarski(B_1774, C_1775) | ~m1_subset_1(C_1775, k1_zfmisc_1(A_1773)) | ~m1_subset_1(B_1774, k1_zfmisc_1(A_1773)))), inference(resolution, [status(thm)], [c_69645, c_40])).
% 27.75/15.60  tff(c_86711, plain, (![B_1774]: (v1_xboole_0('#skF_6'('#skF_7', B_1774, '#skF_7')) | ~v1_xboole_0('#skF_7') | r1_tarski(B_1774, '#skF_7') | ~m1_subset_1(B_1774, k1_zfmisc_1('#skF_7')))), inference(resolution, [status(thm)], [c_71876, c_86677])).
% 27.75/15.60  tff(c_87023, plain, (![B_1778]: (v1_xboole_0('#skF_6'('#skF_7', B_1778, '#skF_7')) | r1_tarski(B_1778, '#skF_7') | ~m1_subset_1(B_1778, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_54021, c_86711])).
% 27.75/15.60  tff(c_87141, plain, (v1_xboole_0('#skF_6'('#skF_7', '#skF_9', '#skF_7')) | r1_tarski('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_52, c_87023])).
% 27.75/15.60  tff(c_87143, plain, (r1_tarski('#skF_9', '#skF_7')), inference(splitLeft, [status(thm)], [c_87141])).
% 27.75/15.60  tff(c_245, plain, (![A_83, A_84]: (~v1_xboole_0(A_83) | ~r2_xboole_0(A_84, k3_tarski(A_83)))), inference(resolution, [status(thm)], [c_10, c_226])).
% 27.75/15.60  tff(c_253, plain, (![A_83, A_1]: (~v1_xboole_0(A_83) | k3_tarski(A_83)=A_1 | ~r1_tarski(A_1, k3_tarski(A_83)))), inference(resolution, [status(thm)], [c_2, c_245])).
% 27.75/15.60  tff(c_54061, plain, (![A_1]: (~v1_xboole_0('#skF_7') | k3_tarski('#skF_7')=A_1 | ~r1_tarski(A_1, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_54032, c_253])).
% 27.75/15.60  tff(c_54099, plain, (![A_1]: (A_1='#skF_7' | ~r1_tarski(A_1, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_54032, c_54021, c_54061])).
% 27.75/15.60  tff(c_87153, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_87143, c_54099])).
% 27.75/15.60  tff(c_87244, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_87153, c_54021])).
% 27.75/15.60  tff(c_87259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_87244])).
% 27.75/15.60  tff(c_87261, plain, (~r1_tarski('#skF_9', '#skF_7')), inference(splitRight, [status(thm)], [c_87141])).
% 27.75/15.60  tff(c_87260, plain, (v1_xboole_0('#skF_6'('#skF_7', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_87141])).
% 27.75/15.60  tff(c_54304, plain, (![B_1296]: (~v1_xboole_0(B_1296) | B_1296='#skF_7')), inference(resolution, [status(thm)], [c_54244, c_12])).
% 27.75/15.60  tff(c_87326, plain, ('#skF_6'('#skF_7', '#skF_9', '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_87260, c_54304])).
% 27.75/15.60  tff(c_87341, plain, (r2_hidden('#skF_7', '#skF_9') | r1_tarski('#skF_9', '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_87326, c_46])).
% 27.75/15.60  tff(c_87354, plain, (r2_hidden('#skF_7', '#skF_9') | r1_tarski('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_71876, c_87341])).
% 27.75/15.60  tff(c_87355, plain, (r2_hidden('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_87261, c_87354])).
% 27.75/15.60  tff(c_170, plain, (![C_70, A_28, B_29]: (r2_hidden(C_70, k3_tarski(A_28)) | ~r2_hidden(C_70, B_29) | ~m1_subset_1(B_29, A_28) | v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_36, c_163])).
% 27.75/15.60  tff(c_88061, plain, (![A_1794]: (r2_hidden('#skF_7', k3_tarski(A_1794)) | ~m1_subset_1('#skF_9', A_1794) | v1_xboole_0(A_1794))), inference(resolution, [status(thm)], [c_87355, c_170])).
% 27.75/15.60  tff(c_88180, plain, (![A_27]: (r2_hidden('#skF_7', A_27) | ~m1_subset_1('#skF_9', k1_zfmisc_1(A_27)) | v1_xboole_0(k1_zfmisc_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_88061])).
% 27.75/15.60  tff(c_88208, plain, (![A_1795]: (r2_hidden('#skF_7', A_1795) | ~m1_subset_1('#skF_9', k1_zfmisc_1(A_1795)))), inference(negUnitSimplification, [status(thm)], [c_42, c_88180])).
% 27.75/15.60  tff(c_88214, plain, (r2_hidden('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_52, c_88208])).
% 27.75/15.60  tff(c_88219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54092, c_88214])).
% 27.75/15.60  tff(c_88221, plain, (m1_subset_1('#skF_9', '#skF_7')), inference(splitRight, [status(thm)], [c_54190])).
% 27.75/15.60  tff(c_88224, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_88221, c_40])).
% 27.75/15.60  tff(c_88227, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_54021, c_88224])).
% 27.75/15.60  tff(c_88229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_88227])).
% 27.75/15.60  tff(c_88231, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_424])).
% 27.75/15.60  tff(c_88232, plain, (![A_1796, B_1797]: (r2_hidden('#skF_3'(A_1796, B_1797), A_1796) | r2_hidden('#skF_4'(A_1796, B_1797), B_1797) | k3_tarski(A_1796)=B_1797)), inference(cnfTransformation, [status(thm)], [f_57])).
% 27.75/15.60  tff(c_88347, plain, (![B_1803, A_1804]: (~v1_xboole_0(B_1803) | r2_hidden('#skF_3'(A_1804, B_1803), A_1804) | k3_tarski(A_1804)=B_1803)), inference(resolution, [status(thm)], [c_88232, c_12])).
% 27.75/15.60  tff(c_88392, plain, (![A_1805, B_1806]: (~v1_xboole_0(A_1805) | ~v1_xboole_0(B_1806) | k3_tarski(A_1805)=B_1806)), inference(resolution, [status(thm)], [c_88347, c_12])).
% 27.75/15.60  tff(c_88396, plain, (![B_1807]: (~v1_xboole_0(B_1807) | k3_tarski('#skF_8')=B_1807)), inference(resolution, [status(thm)], [c_88231, c_88392])).
% 27.75/15.60  tff(c_88400, plain, (k3_tarski('#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_88231, c_88396])).
% 27.75/15.60  tff(c_315, plain, (![A_90, C_23]: (~v1_xboole_0(A_90) | ~r2_hidden(C_23, k3_tarski(k3_tarski(k3_tarski(k3_tarski(A_90))))))), inference(resolution, [status(thm)], [c_16, c_299])).
% 27.75/15.60  tff(c_88423, plain, (![C_23]: (~v1_xboole_0('#skF_8') | ~r2_hidden(C_23, k3_tarski(k3_tarski(k3_tarski('#skF_8')))))), inference(superposition, [status(thm), theory('equality')], [c_88400, c_315])).
% 27.75/15.60  tff(c_88459, plain, (![C_23]: (~r2_hidden(C_23, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88400, c_88400, c_88400, c_88231, c_88423])).
% 27.75/15.60  tff(c_88479, plain, (![D_42]: (~r2_hidden(D_42, '#skF_9') | ~m1_subset_1(D_42, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_88459, c_56])).
% 27.75/15.60  tff(c_102530, plain, (![A_2032, C_2033]: (~m1_subset_1('#skF_6'(A_2032, '#skF_9', C_2033), '#skF_7') | r1_tarski('#skF_9', C_2033) | ~m1_subset_1(C_2033, k1_zfmisc_1(A_2032)) | ~m1_subset_1('#skF_9', k1_zfmisc_1(A_2032)))), inference(resolution, [status(thm)], [c_89166, c_88479])).
% 27.75/15.60  tff(c_102534, plain, (![C_36]: (r1_tarski('#skF_9', C_36) | ~m1_subset_1(C_36, k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1('#skF_7')))), inference(resolution, [status(thm)], [c_48, c_102530])).
% 27.75/15.60  tff(c_102542, plain, (![C_2034]: (r1_tarski('#skF_9', C_2034) | ~m1_subset_1(C_2034, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_102534])).
% 27.75/15.60  tff(c_102641, plain, (r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_54, c_102542])).
% 27.75/15.60  tff(c_88426, plain, (![A_1]: (~v1_xboole_0('#skF_8') | k3_tarski('#skF_8')=A_1 | ~r1_tarski(A_1, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_88400, c_253])).
% 27.75/15.60  tff(c_88461, plain, (![A_1]: (A_1='#skF_8' | ~r1_tarski(A_1, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88400, c_88231, c_88426])).
% 27.75/15.60  tff(c_102646, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_102641, c_88461])).
% 27.75/15.60  tff(c_102654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_102646])).
% 27.75/15.60  tff(c_102655, plain, (![D_52]: (~r2_hidden(D_52, '#skF_8') | ~m1_subset_1(D_52, '#skF_7'))), inference(splitRight, [status(thm)], [c_77])).
% 27.75/15.60  tff(c_124369, plain, (![A_2397, C_2398]: (~m1_subset_1('#skF_6'(A_2397, '#skF_8', C_2398), '#skF_7') | r1_tarski('#skF_8', C_2398) | ~m1_subset_1(C_2398, k1_zfmisc_1(A_2397)) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_2397)))), inference(resolution, [status(thm)], [c_104274, c_102655])).
% 27.75/15.60  tff(c_124373, plain, (![C_36]: (r1_tarski('#skF_8', C_36) | ~m1_subset_1(C_36, k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7')))), inference(resolution, [status(thm)], [c_48, c_124369])).
% 27.75/15.60  tff(c_124394, plain, (![C_2401]: (r1_tarski('#skF_8', C_2401) | ~m1_subset_1(C_2401, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_124373])).
% 27.75/15.60  tff(c_124505, plain, (r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_52, c_124394])).
% 27.75/15.60  tff(c_102656, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_77])).
% 27.75/15.60  tff(c_102818, plain, (![A_2059, B_2060]: (r2_hidden('#skF_3'(A_2059, B_2060), A_2059) | r2_hidden('#skF_4'(A_2059, B_2060), B_2060) | k3_tarski(A_2059)=B_2060)), inference(cnfTransformation, [status(thm)], [f_57])).
% 27.75/15.60  tff(c_103033, plain, (![A_2083, B_2084]: (~v1_xboole_0(A_2083) | r2_hidden('#skF_4'(A_2083, B_2084), B_2084) | k3_tarski(A_2083)=B_2084)), inference(resolution, [status(thm)], [c_102818, c_12])).
% 27.75/15.60  tff(c_103093, plain, (![B_2086, A_2087]: (~v1_xboole_0(B_2086) | ~v1_xboole_0(A_2087) | k3_tarski(A_2087)=B_2086)), inference(resolution, [status(thm)], [c_103033, c_12])).
% 27.75/15.60  tff(c_103097, plain, (![A_2088]: (~v1_xboole_0(A_2088) | k3_tarski(A_2088)='#skF_9')), inference(resolution, [status(thm)], [c_102656, c_103093])).
% 27.75/15.60  tff(c_103101, plain, (k3_tarski('#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_102656, c_103097])).
% 27.75/15.60  tff(c_102792, plain, (![A_2057, C_2058]: (r2_hidden('#skF_5'(A_2057, k3_tarski(A_2057), C_2058), A_2057) | ~r2_hidden(C_2058, k3_tarski(A_2057)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 27.75/15.60  tff(c_102855, plain, (![A_2061, C_2062]: (~v1_xboole_0(A_2061) | ~r2_hidden(C_2062, k3_tarski(A_2061)))), inference(resolution, [status(thm)], [c_102792, c_12])).
% 27.75/15.60  tff(c_102884, plain, (![A_2063, A_2064]: (~v1_xboole_0(A_2063) | ~r2_xboole_0(A_2064, k3_tarski(A_2063)))), inference(resolution, [status(thm)], [c_10, c_102855])).
% 27.75/15.60  tff(c_102892, plain, (![A_2063, A_1]: (~v1_xboole_0(A_2063) | k3_tarski(A_2063)=A_1 | ~r1_tarski(A_1, k3_tarski(A_2063)))), inference(resolution, [status(thm)], [c_2, c_102884])).
% 27.75/15.60  tff(c_103111, plain, (![A_1]: (~v1_xboole_0('#skF_9') | k3_tarski('#skF_9')=A_1 | ~r1_tarski(A_1, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_103101, c_102892])).
% 27.75/15.60  tff(c_103149, plain, (![A_1]: (A_1='#skF_9' | ~r1_tarski(A_1, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_103101, c_102656, c_103111])).
% 27.75/15.60  tff(c_124514, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_124505, c_103149])).
% 27.75/15.60  tff(c_124523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_124514])).
% 27.75/15.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.75/15.60  
% 27.75/15.60  Inference rules
% 27.75/15.60  ----------------------
% 27.75/15.60  #Ref     : 0
% 27.75/15.60  #Sup     : 33264
% 27.75/15.60  #Fact    : 0
% 27.75/15.60  #Define  : 0
% 27.75/15.60  #Split   : 117
% 27.75/15.60  #Chain   : 0
% 27.75/15.60  #Close   : 0
% 27.75/15.60  
% 27.75/15.60  Ordering : KBO
% 27.75/15.60  
% 27.75/15.60  Simplification rules
% 27.75/15.60  ----------------------
% 27.75/15.60  #Subsume      : 18570
% 27.75/15.60  #Demod        : 15872
% 27.75/15.60  #Tautology    : 2731
% 27.75/15.60  #SimpNegUnit  : 2122
% 27.75/15.60  #BackRed      : 393
% 27.75/15.60  
% 27.75/15.60  #Partial instantiations: 0
% 27.75/15.60  #Strategies tried      : 1
% 27.75/15.60  
% 27.75/15.60  Timing (in seconds)
% 27.75/15.60  ----------------------
% 27.75/15.61  Preprocessing        : 0.33
% 27.75/15.61  Parsing              : 0.17
% 27.75/15.61  CNF conversion       : 0.03
% 27.75/15.61  Main loop            : 14.40
% 27.75/15.61  Inferencing          : 2.46
% 27.75/15.61  Reduction            : 3.09
% 27.75/15.61  Demodulation         : 2.02
% 27.75/15.61  BG Simplification    : 0.27
% 27.75/15.61  Subsumption          : 7.81
% 27.75/15.61  Abstraction          : 0.47
% 27.75/15.61  MUC search           : 0.00
% 27.75/15.61  Cooper               : 0.00
% 27.75/15.61  Total                : 14.86
% 27.75/15.61  Index Insertion      : 0.00
% 27.75/15.61  Index Deletion       : 0.00
% 27.75/15.61  Index Matching       : 0.00
% 27.75/15.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
