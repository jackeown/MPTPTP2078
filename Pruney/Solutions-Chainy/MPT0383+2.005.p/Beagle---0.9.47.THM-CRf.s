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
% DateTime   : Thu Dec  3 09:57:07 EST 2020

% Result     : Theorem 22.68s
% Output     : CNFRefutation 22.80s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 745 expanded)
%              Number of leaves         :   26 ( 257 expanded)
%              Depth                    :   18
%              Number of atoms          :  231 (1716 expanded)
%              Number of equality atoms :   27 ( 312 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r2_hidden(D,C)
          & r1_tarski(C,k2_zfmisc_1(A,B))
          & ! [E] :
              ( m1_subset_1(E,A)
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => D != k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_46,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_47,plain,(
    ! [B_30,A_31] :
      ( ~ r2_hidden(B_30,A_31)
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_47])).

tff(c_73,plain,(
    ! [B_41,A_42] :
      ( m1_subset_1(B_41,A_42)
      | ~ r2_hidden(B_41,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_79,plain,
    ( m1_subset_1('#skF_9','#skF_8')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_73])).

tff(c_83,plain,(
    m1_subset_1('#skF_9','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_79])).

tff(c_44,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_58,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = A_35
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_62,plain,(
    k3_xboole_0('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_44,c_58])).

tff(c_36,plain,(
    ! [B_23,A_22] :
      ( r2_hidden(B_23,A_22)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_116,plain,(
    ! [D_49,B_50,A_51] :
      ( r2_hidden(D_49,B_50)
      | ~ r2_hidden(D_49,k3_xboole_0(A_51,B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_358,plain,(
    ! [B_96,B_97,A_98] :
      ( r2_hidden(B_96,B_97)
      | ~ m1_subset_1(B_96,k3_xboole_0(A_98,B_97))
      | v1_xboole_0(k3_xboole_0(A_98,B_97)) ) ),
    inference(resolution,[status(thm)],[c_36,c_116])).

tff(c_369,plain,(
    ! [B_96] :
      ( r2_hidden(B_96,k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_96,'#skF_8')
      | v1_xboole_0(k3_xboole_0('#skF_8',k2_zfmisc_1('#skF_6','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_358])).

tff(c_372,plain,(
    ! [B_96] :
      ( r2_hidden(B_96,k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_96,'#skF_8')
      | v1_xboole_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_369])).

tff(c_373,plain,(
    ! [B_96] :
      ( r2_hidden(B_96,k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_96,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_372])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_213,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_76,B_77)),B_77)
      | v1_xboole_0(k3_xboole_0(A_76,B_77)) ) ),
    inference(resolution,[status(thm)],[c_4,c_116])).

tff(c_230,plain,
    ( r2_hidden('#skF_1'('#skF_8'),k2_zfmisc_1('#skF_6','#skF_7'))
    | v1_xboole_0(k3_xboole_0('#skF_8',k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_213])).

tff(c_235,plain,
    ( r2_hidden('#skF_1'('#skF_8'),k2_zfmisc_1('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_230])).

tff(c_236,plain,(
    r2_hidden('#skF_1'('#skF_8'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_235])).

tff(c_440,plain,(
    ! [A_105,B_106,C_107] :
      ( k4_tarski('#skF_4'(A_105,B_106,C_107),'#skF_5'(A_105,B_106,C_107)) = A_105
      | ~ r2_hidden(A_105,k2_zfmisc_1(B_106,C_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [B_19,D_21,A_18,C_20] :
      ( r2_hidden(B_19,D_21)
      | ~ r2_hidden(k4_tarski(A_18,B_19),k2_zfmisc_1(C_20,D_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10611,plain,(
    ! [D_803,B_801,C_802,C_799,A_800] :
      ( r2_hidden('#skF_5'(A_800,B_801,C_802),D_803)
      | ~ r2_hidden(A_800,k2_zfmisc_1(C_799,D_803))
      | ~ r2_hidden(A_800,k2_zfmisc_1(B_801,C_802)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_30])).

tff(c_10946,plain,(
    ! [B_855,C_856] :
      ( r2_hidden('#skF_5'('#skF_1'('#skF_8'),B_855,C_856),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_8'),k2_zfmisc_1(B_855,C_856)) ) ),
    inference(resolution,[status(thm)],[c_236,c_10611])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10954,plain,(
    ! [B_855,C_856] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_8'),k2_zfmisc_1(B_855,C_856)) ) ),
    inference(resolution,[status(thm)],[c_10946,c_2])).

tff(c_10955,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_10954])).

tff(c_18810,plain,(
    ! [B_1480,B_1481,C_1482] :
      ( r2_hidden('#skF_5'(B_1480,B_1481,C_1482),'#skF_7')
      | ~ r2_hidden(B_1480,k2_zfmisc_1(B_1481,C_1482))
      | ~ m1_subset_1(B_1480,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_373,c_10611])).

tff(c_34,plain,(
    ! [B_23,A_22] :
      ( m1_subset_1(B_23,A_22)
      | ~ r2_hidden(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18813,plain,(
    ! [B_1480,B_1481,C_1482] :
      ( m1_subset_1('#skF_5'(B_1480,B_1481,C_1482),'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ r2_hidden(B_1480,k2_zfmisc_1(B_1481,C_1482))
      | ~ m1_subset_1(B_1480,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_18810,c_34])).

tff(c_91640,plain,(
    ! [B_6492,B_6493,C_6494] :
      ( m1_subset_1('#skF_5'(B_6492,B_6493,C_6494),'#skF_7')
      | ~ r2_hidden(B_6492,k2_zfmisc_1(B_6493,C_6494))
      | ~ m1_subset_1(B_6492,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_10955,c_18813])).

tff(c_92062,plain,(
    ! [B_96] :
      ( m1_subset_1('#skF_5'(B_96,'#skF_6','#skF_7'),'#skF_7')
      | ~ m1_subset_1(B_96,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_373,c_91640])).

tff(c_123,plain,(
    ! [D_49] :
      ( r2_hidden(D_49,k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(D_49,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_116])).

tff(c_42,plain,(
    ! [E_27,F_29] :
      ( k4_tarski(E_27,F_29) != '#skF_9'
      | ~ m1_subset_1(F_29,'#skF_7')
      | ~ m1_subset_1(E_27,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_536,plain,(
    ! [A_119,B_120,C_121] :
      ( A_119 != '#skF_9'
      | ~ m1_subset_1('#skF_5'(A_119,B_120,C_121),'#skF_7')
      | ~ m1_subset_1('#skF_4'(A_119,B_120,C_121),'#skF_6')
      | ~ r2_hidden(A_119,k2_zfmisc_1(B_120,C_121)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_42])).

tff(c_573,plain,
    ( '#skF_1'('#skF_8') != '#skF_9'
    | ~ m1_subset_1('#skF_5'('#skF_1'('#skF_8'),'#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_4'('#skF_1'('#skF_8'),'#skF_6','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_236,c_536])).

tff(c_1538,plain,(
    ~ m1_subset_1('#skF_4'('#skF_1'('#skF_8'),'#skF_6','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_573])).

tff(c_102,plain,(
    ! [D_46,A_47,B_48] :
      ( r2_hidden(D_46,A_47)
      | ~ r2_hidden(D_46,k3_xboole_0(A_47,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_259,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_80,B_81)),A_80)
      | v1_xboole_0(k3_xboole_0(A_80,B_81)) ) ),
    inference(resolution,[status(thm)],[c_4,c_102])).

tff(c_276,plain,
    ( r2_hidden('#skF_1'('#skF_8'),'#skF_8')
    | v1_xboole_0(k3_xboole_0('#skF_8',k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_259])).

tff(c_281,plain,
    ( r2_hidden('#skF_1'('#skF_8'),'#skF_8')
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_276])).

tff(c_282,plain,(
    r2_hidden('#skF_1'('#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_281])).

tff(c_285,plain,
    ( m1_subset_1('#skF_1'('#skF_8'),'#skF_8')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_282,c_34])).

tff(c_291,plain,(
    m1_subset_1('#skF_1'('#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_285])).

tff(c_38,plain,(
    ! [B_23,A_22] :
      ( m1_subset_1(B_23,A_22)
      | ~ v1_xboole_0(B_23)
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1542,plain,
    ( ~ v1_xboole_0('#skF_4'('#skF_1'('#skF_8'),'#skF_6','#skF_7'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_1538])).

tff(c_1543,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1542])).

tff(c_32,plain,(
    ! [A_18,C_20,B_19,D_21] :
      ( r2_hidden(A_18,C_20)
      | ~ r2_hidden(k4_tarski(A_18,B_19),k2_zfmisc_1(C_20,D_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2932,plain,(
    ! [C_371,A_372,D_375,C_374,B_373] :
      ( r2_hidden('#skF_4'(A_372,B_373,C_374),C_371)
      | ~ r2_hidden(A_372,k2_zfmisc_1(C_371,D_375))
      | ~ r2_hidden(A_372,k2_zfmisc_1(B_373,C_374)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_32])).

tff(c_3031,plain,(
    ! [B_382,C_383] :
      ( r2_hidden('#skF_4'('#skF_1'('#skF_8'),B_382,C_383),'#skF_6')
      | ~ r2_hidden('#skF_1'('#skF_8'),k2_zfmisc_1(B_382,C_383)) ) ),
    inference(resolution,[status(thm)],[c_236,c_2932])).

tff(c_3034,plain,(
    ! [B_382,C_383] :
      ( m1_subset_1('#skF_4'('#skF_1'('#skF_8'),B_382,C_383),'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ r2_hidden('#skF_1'('#skF_8'),k2_zfmisc_1(B_382,C_383)) ) ),
    inference(resolution,[status(thm)],[c_3031,c_34])).

tff(c_3106,plain,(
    ! [B_386,C_387] :
      ( m1_subset_1('#skF_4'('#skF_1'('#skF_8'),B_386,C_387),'#skF_6')
      | ~ r2_hidden('#skF_1'('#skF_8'),k2_zfmisc_1(B_386,C_387)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1543,c_3034])).

tff(c_3110,plain,
    ( m1_subset_1('#skF_4'('#skF_1'('#skF_8'),'#skF_6','#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_373,c_3106])).

tff(c_3123,plain,(
    m1_subset_1('#skF_4'('#skF_1'('#skF_8'),'#skF_6','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_3110])).

tff(c_3125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1538,c_3123])).

tff(c_3127,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1542])).

tff(c_5617,plain,(
    ! [C_493,A_491,B_492,C_490,D_494] :
      ( r2_hidden('#skF_4'(A_491,B_492,C_493),C_490)
      | ~ r2_hidden(A_491,k2_zfmisc_1(C_490,D_494))
      | ~ r2_hidden(A_491,k2_zfmisc_1(B_492,C_493)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_32])).

tff(c_9358,plain,(
    ! [B_677,C_678] :
      ( r2_hidden('#skF_4'('#skF_1'('#skF_8'),B_677,C_678),'#skF_6')
      | ~ r2_hidden('#skF_1'('#skF_8'),k2_zfmisc_1(B_677,C_678)) ) ),
    inference(resolution,[status(thm)],[c_236,c_5617])).

tff(c_9373,plain,(
    ! [B_677,C_678] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ r2_hidden('#skF_1'('#skF_8'),k2_zfmisc_1(B_677,C_678)) ) ),
    inference(resolution,[status(thm)],[c_9358,c_2])).

tff(c_9382,plain,(
    ! [B_677,C_678] : ~ r2_hidden('#skF_1'('#skF_8'),k2_zfmisc_1(B_677,C_678)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3127,c_9373])).

tff(c_9384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9382,c_236])).

tff(c_9386,plain,(
    m1_subset_1('#skF_4'('#skF_1'('#skF_8'),'#skF_6','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_573])).

tff(c_40,plain,(
    ! [B_23,A_22] :
      ( v1_xboole_0(B_23)
      | ~ m1_subset_1(B_23,A_22)
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_9414,plain,
    ( v1_xboole_0('#skF_4'('#skF_1'('#skF_8'),'#skF_6','#skF_7'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_9386,c_40])).

tff(c_9415,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_9414])).

tff(c_10858,plain,(
    ! [D_854,B_852,C_853,C_850,A_851] :
      ( r2_hidden('#skF_4'(A_851,B_852,C_853),C_850)
      | ~ r2_hidden(A_851,k2_zfmisc_1(C_850,D_854))
      | ~ r2_hidden(A_851,k2_zfmisc_1(B_852,C_853)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_32])).

tff(c_18712,plain,(
    ! [D_1471,B_1472,C_1473] :
      ( r2_hidden('#skF_4'(D_1471,B_1472,C_1473),'#skF_6')
      | ~ r2_hidden(D_1471,k2_zfmisc_1(B_1472,C_1473))
      | ~ r2_hidden(D_1471,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_123,c_10858])).

tff(c_18715,plain,(
    ! [D_1471,B_1472,C_1473] :
      ( m1_subset_1('#skF_4'(D_1471,B_1472,C_1473),'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ r2_hidden(D_1471,k2_zfmisc_1(B_1472,C_1473))
      | ~ r2_hidden(D_1471,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_18712,c_34])).

tff(c_92381,plain,(
    ! [D_6537,B_6538,C_6539] :
      ( m1_subset_1('#skF_4'(D_6537,B_6538,C_6539),'#skF_6')
      | ~ r2_hidden(D_6537,k2_zfmisc_1(B_6538,C_6539))
      | ~ r2_hidden(D_6537,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_9415,c_18715])).

tff(c_92815,plain,(
    ! [D_6543] :
      ( m1_subset_1('#skF_4'(D_6543,'#skF_6','#skF_7'),'#skF_6')
      | ~ r2_hidden(D_6543,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_123,c_92381])).

tff(c_575,plain,(
    ! [D_49] :
      ( D_49 != '#skF_9'
      | ~ m1_subset_1('#skF_5'(D_49,'#skF_6','#skF_7'),'#skF_7')
      | ~ m1_subset_1('#skF_4'(D_49,'#skF_6','#skF_7'),'#skF_6')
      | ~ r2_hidden(D_49,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_123,c_536])).

tff(c_93285,plain,(
    ! [D_6572] :
      ( D_6572 != '#skF_9'
      | ~ m1_subset_1('#skF_5'(D_6572,'#skF_6','#skF_7'),'#skF_7')
      | ~ r2_hidden(D_6572,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_92815,c_575])).

tff(c_93388,plain,(
    ! [B_6573] :
      ( B_6573 != '#skF_9'
      | ~ r2_hidden(B_6573,'#skF_8')
      | ~ m1_subset_1(B_6573,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_92062,c_93285])).

tff(c_93631,plain,(
    ~ m1_subset_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_93388])).

tff(c_93752,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_93631])).

tff(c_93753,plain,(
    ! [B_855,C_856] : ~ r2_hidden('#skF_1'('#skF_8'),k2_zfmisc_1(B_855,C_856)) ),
    inference(splitRight,[status(thm)],[c_10954])).

tff(c_94161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93753,c_236])).

tff(c_94163,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_9414])).

tff(c_94162,plain,(
    v1_xboole_0('#skF_4'('#skF_1'('#skF_8'),'#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_9414])).

tff(c_20,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_2'(A_5,B_6,C_7),B_6)
      | r2_hidden('#skF_3'(A_5,B_6,C_7),C_7)
      | k3_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_885,plain,(
    ! [A_165,B_166,C_167] :
      ( ~ r2_hidden('#skF_2'(A_165,B_166,C_167),C_167)
      | r2_hidden('#skF_3'(A_165,B_166,C_167),C_167)
      | k3_xboole_0(A_165,B_166) = C_167 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_921,plain,(
    ! [A_168,B_169] :
      ( r2_hidden('#skF_3'(A_168,B_169,B_169),B_169)
      | k3_xboole_0(A_168,B_169) = B_169 ) ),
    inference(resolution,[status(thm)],[c_20,c_885])).

tff(c_952,plain,(
    ! [B_169,A_168] :
      ( ~ v1_xboole_0(B_169)
      | k3_xboole_0(A_168,B_169) = B_169 ) ),
    inference(resolution,[status(thm)],[c_921,c_2])).

tff(c_94191,plain,(
    ! [A_168] : k3_xboole_0(A_168,'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_94163,c_952])).

tff(c_663,plain,(
    ! [A_134,B_135,C_136] :
      ( r2_hidden('#skF_2'(A_134,B_135,C_136),B_135)
      | r2_hidden('#skF_3'(A_134,B_135,C_136),C_136)
      | k3_xboole_0(A_134,B_135) = C_136 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_840,plain,(
    ! [C_159,A_160,B_161] :
      ( ~ v1_xboole_0(C_159)
      | r2_hidden('#skF_2'(A_160,B_161,C_159),B_161)
      | k3_xboole_0(A_160,B_161) = C_159 ) ),
    inference(resolution,[status(thm)],[c_663,c_2])).

tff(c_871,plain,(
    ! [B_161,C_159,A_160] :
      ( ~ v1_xboole_0(B_161)
      | ~ v1_xboole_0(C_159)
      | k3_xboole_0(A_160,B_161) = C_159 ) ),
    inference(resolution,[status(thm)],[c_840,c_2])).

tff(c_94192,plain,(
    ! [C_159,A_160] :
      ( ~ v1_xboole_0(C_159)
      | k3_xboole_0(A_160,'#skF_6') = C_159 ) ),
    inference(resolution,[status(thm)],[c_94163,c_871])).

tff(c_94524,plain,(
    ! [C_6591] :
      ( ~ v1_xboole_0(C_6591)
      | C_6591 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94191,c_94192])).

tff(c_94543,plain,(
    '#skF_4'('#skF_1'('#skF_8'),'#skF_6','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_94162,c_94524])).

tff(c_26,plain,(
    ! [A_13,B_14,C_15] :
      ( k4_tarski('#skF_4'(A_13,B_14,C_15),'#skF_5'(A_13,B_14,C_15)) = A_13
      | ~ r2_hidden(A_13,k2_zfmisc_1(B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_94572,plain,
    ( k4_tarski('#skF_6','#skF_5'('#skF_1'('#skF_8'),'#skF_6','#skF_7')) = '#skF_1'('#skF_8')
    | ~ r2_hidden('#skF_1'('#skF_8'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_94543,c_26])).

tff(c_94583,plain,(
    k4_tarski('#skF_6','#skF_5'('#skF_1'('#skF_8'),'#skF_6','#skF_7')) = '#skF_1'('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_94572])).

tff(c_168,plain,(
    ! [A_62,C_63,B_64,D_65] :
      ( r2_hidden(A_62,C_63)
      | ~ r2_hidden(k4_tarski(A_62,B_64),k2_zfmisc_1(C_63,D_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_178,plain,(
    ! [A_66,B_67] :
      ( r2_hidden(A_66,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_66,B_67),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_123,c_168])).

tff(c_181,plain,(
    ! [A_66,B_67] :
      ( r2_hidden(A_66,'#skF_6')
      | ~ m1_subset_1(k4_tarski(A_66,B_67),'#skF_8')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36,c_178])).

tff(c_184,plain,(
    ! [A_66,B_67] :
      ( r2_hidden(A_66,'#skF_6')
      | ~ m1_subset_1(k4_tarski(A_66,B_67),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_181])).

tff(c_95833,plain,
    ( r2_hidden('#skF_6','#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_8'),'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_94583,c_184])).

tff(c_95855,plain,(
    r2_hidden('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_95833])).

tff(c_95982,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_95855,c_2])).

tff(c_95990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94163,c_95982])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.68/13.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.68/13.49  
% 22.68/13.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.68/13.49  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 22.68/13.49  
% 22.68/13.49  %Foreground sorts:
% 22.68/13.49  
% 22.68/13.49  
% 22.68/13.49  %Background operators:
% 22.68/13.49  
% 22.68/13.49  
% 22.68/13.49  %Foreground operators:
% 22.68/13.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.68/13.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.68/13.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 22.68/13.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 22.68/13.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 22.68/13.49  tff('#skF_7', type, '#skF_7': $i).
% 22.68/13.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.68/13.49  tff('#skF_6', type, '#skF_6': $i).
% 22.68/13.49  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 22.68/13.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 22.68/13.49  tff('#skF_9', type, '#skF_9': $i).
% 22.68/13.49  tff('#skF_8', type, '#skF_8': $i).
% 22.68/13.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.68/13.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 22.68/13.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 22.68/13.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.68/13.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 22.68/13.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 22.68/13.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.68/13.49  
% 22.80/13.51  tff(f_85, negated_conjecture, ~(![A, B, C, D]: ~((r2_hidden(D, C) & r1_tarski(C, k2_zfmisc_1(A, B))) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => ~(D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_subset_1)).
% 22.80/13.51  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 22.80/13.51  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 22.80/13.51  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 22.80/13.51  tff(f_40, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 22.80/13.51  tff(f_51, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 22.80/13.51  tff(f_57, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 22.80/13.51  tff(c_46, plain, (r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_85])).
% 22.80/13.51  tff(c_47, plain, (![B_30, A_31]: (~r2_hidden(B_30, A_31) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.80/13.51  tff(c_51, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_46, c_47])).
% 22.80/13.51  tff(c_73, plain, (![B_41, A_42]: (m1_subset_1(B_41, A_42) | ~r2_hidden(B_41, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_70])).
% 22.80/13.51  tff(c_79, plain, (m1_subset_1('#skF_9', '#skF_8') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_46, c_73])).
% 22.80/13.51  tff(c_83, plain, (m1_subset_1('#skF_9', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_51, c_79])).
% 22.80/13.51  tff(c_44, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 22.80/13.51  tff(c_58, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=A_35 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_44])).
% 22.80/13.51  tff(c_62, plain, (k3_xboole_0('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))='#skF_8'), inference(resolution, [status(thm)], [c_44, c_58])).
% 22.80/13.51  tff(c_36, plain, (![B_23, A_22]: (r2_hidden(B_23, A_22) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_70])).
% 22.80/13.51  tff(c_116, plain, (![D_49, B_50, A_51]: (r2_hidden(D_49, B_50) | ~r2_hidden(D_49, k3_xboole_0(A_51, B_50)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 22.80/13.51  tff(c_358, plain, (![B_96, B_97, A_98]: (r2_hidden(B_96, B_97) | ~m1_subset_1(B_96, k3_xboole_0(A_98, B_97)) | v1_xboole_0(k3_xboole_0(A_98, B_97)))), inference(resolution, [status(thm)], [c_36, c_116])).
% 22.80/13.51  tff(c_369, plain, (![B_96]: (r2_hidden(B_96, k2_zfmisc_1('#skF_6', '#skF_7')) | ~m1_subset_1(B_96, '#skF_8') | v1_xboole_0(k3_xboole_0('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_62, c_358])).
% 22.80/13.51  tff(c_372, plain, (![B_96]: (r2_hidden(B_96, k2_zfmisc_1('#skF_6', '#skF_7')) | ~m1_subset_1(B_96, '#skF_8') | v1_xboole_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_369])).
% 22.80/13.51  tff(c_373, plain, (![B_96]: (r2_hidden(B_96, k2_zfmisc_1('#skF_6', '#skF_7')) | ~m1_subset_1(B_96, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_51, c_372])).
% 22.80/13.51  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.80/13.51  tff(c_213, plain, (![A_76, B_77]: (r2_hidden('#skF_1'(k3_xboole_0(A_76, B_77)), B_77) | v1_xboole_0(k3_xboole_0(A_76, B_77)))), inference(resolution, [status(thm)], [c_4, c_116])).
% 22.80/13.51  tff(c_230, plain, (r2_hidden('#skF_1'('#skF_8'), k2_zfmisc_1('#skF_6', '#skF_7')) | v1_xboole_0(k3_xboole_0('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_62, c_213])).
% 22.80/13.51  tff(c_235, plain, (r2_hidden('#skF_1'('#skF_8'), k2_zfmisc_1('#skF_6', '#skF_7')) | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_230])).
% 22.80/13.51  tff(c_236, plain, (r2_hidden('#skF_1'('#skF_8'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_51, c_235])).
% 22.80/13.51  tff(c_440, plain, (![A_105, B_106, C_107]: (k4_tarski('#skF_4'(A_105, B_106, C_107), '#skF_5'(A_105, B_106, C_107))=A_105 | ~r2_hidden(A_105, k2_zfmisc_1(B_106, C_107)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 22.80/13.51  tff(c_30, plain, (![B_19, D_21, A_18, C_20]: (r2_hidden(B_19, D_21) | ~r2_hidden(k4_tarski(A_18, B_19), k2_zfmisc_1(C_20, D_21)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 22.80/13.51  tff(c_10611, plain, (![D_803, B_801, C_802, C_799, A_800]: (r2_hidden('#skF_5'(A_800, B_801, C_802), D_803) | ~r2_hidden(A_800, k2_zfmisc_1(C_799, D_803)) | ~r2_hidden(A_800, k2_zfmisc_1(B_801, C_802)))), inference(superposition, [status(thm), theory('equality')], [c_440, c_30])).
% 22.80/13.51  tff(c_10946, plain, (![B_855, C_856]: (r2_hidden('#skF_5'('#skF_1'('#skF_8'), B_855, C_856), '#skF_7') | ~r2_hidden('#skF_1'('#skF_8'), k2_zfmisc_1(B_855, C_856)))), inference(resolution, [status(thm)], [c_236, c_10611])).
% 22.80/13.51  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.80/13.51  tff(c_10954, plain, (![B_855, C_856]: (~v1_xboole_0('#skF_7') | ~r2_hidden('#skF_1'('#skF_8'), k2_zfmisc_1(B_855, C_856)))), inference(resolution, [status(thm)], [c_10946, c_2])).
% 22.80/13.51  tff(c_10955, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_10954])).
% 22.80/13.51  tff(c_18810, plain, (![B_1480, B_1481, C_1482]: (r2_hidden('#skF_5'(B_1480, B_1481, C_1482), '#skF_7') | ~r2_hidden(B_1480, k2_zfmisc_1(B_1481, C_1482)) | ~m1_subset_1(B_1480, '#skF_8'))), inference(resolution, [status(thm)], [c_373, c_10611])).
% 22.80/13.51  tff(c_34, plain, (![B_23, A_22]: (m1_subset_1(B_23, A_22) | ~r2_hidden(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_70])).
% 22.80/13.51  tff(c_18813, plain, (![B_1480, B_1481, C_1482]: (m1_subset_1('#skF_5'(B_1480, B_1481, C_1482), '#skF_7') | v1_xboole_0('#skF_7') | ~r2_hidden(B_1480, k2_zfmisc_1(B_1481, C_1482)) | ~m1_subset_1(B_1480, '#skF_8'))), inference(resolution, [status(thm)], [c_18810, c_34])).
% 22.80/13.51  tff(c_91640, plain, (![B_6492, B_6493, C_6494]: (m1_subset_1('#skF_5'(B_6492, B_6493, C_6494), '#skF_7') | ~r2_hidden(B_6492, k2_zfmisc_1(B_6493, C_6494)) | ~m1_subset_1(B_6492, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_10955, c_18813])).
% 22.80/13.51  tff(c_92062, plain, (![B_96]: (m1_subset_1('#skF_5'(B_96, '#skF_6', '#skF_7'), '#skF_7') | ~m1_subset_1(B_96, '#skF_8'))), inference(resolution, [status(thm)], [c_373, c_91640])).
% 22.80/13.51  tff(c_123, plain, (![D_49]: (r2_hidden(D_49, k2_zfmisc_1('#skF_6', '#skF_7')) | ~r2_hidden(D_49, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_116])).
% 22.80/13.51  tff(c_42, plain, (![E_27, F_29]: (k4_tarski(E_27, F_29)!='#skF_9' | ~m1_subset_1(F_29, '#skF_7') | ~m1_subset_1(E_27, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 22.80/13.51  tff(c_536, plain, (![A_119, B_120, C_121]: (A_119!='#skF_9' | ~m1_subset_1('#skF_5'(A_119, B_120, C_121), '#skF_7') | ~m1_subset_1('#skF_4'(A_119, B_120, C_121), '#skF_6') | ~r2_hidden(A_119, k2_zfmisc_1(B_120, C_121)))), inference(superposition, [status(thm), theory('equality')], [c_440, c_42])).
% 22.80/13.51  tff(c_573, plain, ('#skF_1'('#skF_8')!='#skF_9' | ~m1_subset_1('#skF_5'('#skF_1'('#skF_8'), '#skF_6', '#skF_7'), '#skF_7') | ~m1_subset_1('#skF_4'('#skF_1'('#skF_8'), '#skF_6', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_236, c_536])).
% 22.80/13.51  tff(c_1538, plain, (~m1_subset_1('#skF_4'('#skF_1'('#skF_8'), '#skF_6', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_573])).
% 22.80/13.51  tff(c_102, plain, (![D_46, A_47, B_48]: (r2_hidden(D_46, A_47) | ~r2_hidden(D_46, k3_xboole_0(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 22.80/13.51  tff(c_259, plain, (![A_80, B_81]: (r2_hidden('#skF_1'(k3_xboole_0(A_80, B_81)), A_80) | v1_xboole_0(k3_xboole_0(A_80, B_81)))), inference(resolution, [status(thm)], [c_4, c_102])).
% 22.80/13.51  tff(c_276, plain, (r2_hidden('#skF_1'('#skF_8'), '#skF_8') | v1_xboole_0(k3_xboole_0('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_62, c_259])).
% 22.80/13.51  tff(c_281, plain, (r2_hidden('#skF_1'('#skF_8'), '#skF_8') | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_276])).
% 22.80/13.51  tff(c_282, plain, (r2_hidden('#skF_1'('#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_51, c_281])).
% 22.80/13.51  tff(c_285, plain, (m1_subset_1('#skF_1'('#skF_8'), '#skF_8') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_282, c_34])).
% 22.80/13.51  tff(c_291, plain, (m1_subset_1('#skF_1'('#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_51, c_285])).
% 22.80/13.51  tff(c_38, plain, (![B_23, A_22]: (m1_subset_1(B_23, A_22) | ~v1_xboole_0(B_23) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_70])).
% 22.80/13.51  tff(c_1542, plain, (~v1_xboole_0('#skF_4'('#skF_1'('#skF_8'), '#skF_6', '#skF_7')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_38, c_1538])).
% 22.80/13.51  tff(c_1543, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_1542])).
% 22.80/13.51  tff(c_32, plain, (![A_18, C_20, B_19, D_21]: (r2_hidden(A_18, C_20) | ~r2_hidden(k4_tarski(A_18, B_19), k2_zfmisc_1(C_20, D_21)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 22.80/13.51  tff(c_2932, plain, (![C_371, A_372, D_375, C_374, B_373]: (r2_hidden('#skF_4'(A_372, B_373, C_374), C_371) | ~r2_hidden(A_372, k2_zfmisc_1(C_371, D_375)) | ~r2_hidden(A_372, k2_zfmisc_1(B_373, C_374)))), inference(superposition, [status(thm), theory('equality')], [c_440, c_32])).
% 22.80/13.51  tff(c_3031, plain, (![B_382, C_383]: (r2_hidden('#skF_4'('#skF_1'('#skF_8'), B_382, C_383), '#skF_6') | ~r2_hidden('#skF_1'('#skF_8'), k2_zfmisc_1(B_382, C_383)))), inference(resolution, [status(thm)], [c_236, c_2932])).
% 22.80/13.51  tff(c_3034, plain, (![B_382, C_383]: (m1_subset_1('#skF_4'('#skF_1'('#skF_8'), B_382, C_383), '#skF_6') | v1_xboole_0('#skF_6') | ~r2_hidden('#skF_1'('#skF_8'), k2_zfmisc_1(B_382, C_383)))), inference(resolution, [status(thm)], [c_3031, c_34])).
% 22.80/13.51  tff(c_3106, plain, (![B_386, C_387]: (m1_subset_1('#skF_4'('#skF_1'('#skF_8'), B_386, C_387), '#skF_6') | ~r2_hidden('#skF_1'('#skF_8'), k2_zfmisc_1(B_386, C_387)))), inference(negUnitSimplification, [status(thm)], [c_1543, c_3034])).
% 22.80/13.51  tff(c_3110, plain, (m1_subset_1('#skF_4'('#skF_1'('#skF_8'), '#skF_6', '#skF_7'), '#skF_6') | ~m1_subset_1('#skF_1'('#skF_8'), '#skF_8')), inference(resolution, [status(thm)], [c_373, c_3106])).
% 22.80/13.51  tff(c_3123, plain, (m1_subset_1('#skF_4'('#skF_1'('#skF_8'), '#skF_6', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_3110])).
% 22.80/13.51  tff(c_3125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1538, c_3123])).
% 22.80/13.51  tff(c_3127, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_1542])).
% 22.80/13.51  tff(c_5617, plain, (![C_493, A_491, B_492, C_490, D_494]: (r2_hidden('#skF_4'(A_491, B_492, C_493), C_490) | ~r2_hidden(A_491, k2_zfmisc_1(C_490, D_494)) | ~r2_hidden(A_491, k2_zfmisc_1(B_492, C_493)))), inference(superposition, [status(thm), theory('equality')], [c_440, c_32])).
% 22.80/13.51  tff(c_9358, plain, (![B_677, C_678]: (r2_hidden('#skF_4'('#skF_1'('#skF_8'), B_677, C_678), '#skF_6') | ~r2_hidden('#skF_1'('#skF_8'), k2_zfmisc_1(B_677, C_678)))), inference(resolution, [status(thm)], [c_236, c_5617])).
% 22.80/13.51  tff(c_9373, plain, (![B_677, C_678]: (~v1_xboole_0('#skF_6') | ~r2_hidden('#skF_1'('#skF_8'), k2_zfmisc_1(B_677, C_678)))), inference(resolution, [status(thm)], [c_9358, c_2])).
% 22.80/13.51  tff(c_9382, plain, (![B_677, C_678]: (~r2_hidden('#skF_1'('#skF_8'), k2_zfmisc_1(B_677, C_678)))), inference(demodulation, [status(thm), theory('equality')], [c_3127, c_9373])).
% 22.80/13.51  tff(c_9384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9382, c_236])).
% 22.80/13.51  tff(c_9386, plain, (m1_subset_1('#skF_4'('#skF_1'('#skF_8'), '#skF_6', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_573])).
% 22.80/13.51  tff(c_40, plain, (![B_23, A_22]: (v1_xboole_0(B_23) | ~m1_subset_1(B_23, A_22) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_70])).
% 22.80/13.51  tff(c_9414, plain, (v1_xboole_0('#skF_4'('#skF_1'('#skF_8'), '#skF_6', '#skF_7')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_9386, c_40])).
% 22.80/13.51  tff(c_9415, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_9414])).
% 22.80/13.51  tff(c_10858, plain, (![D_854, B_852, C_853, C_850, A_851]: (r2_hidden('#skF_4'(A_851, B_852, C_853), C_850) | ~r2_hidden(A_851, k2_zfmisc_1(C_850, D_854)) | ~r2_hidden(A_851, k2_zfmisc_1(B_852, C_853)))), inference(superposition, [status(thm), theory('equality')], [c_440, c_32])).
% 22.80/13.51  tff(c_18712, plain, (![D_1471, B_1472, C_1473]: (r2_hidden('#skF_4'(D_1471, B_1472, C_1473), '#skF_6') | ~r2_hidden(D_1471, k2_zfmisc_1(B_1472, C_1473)) | ~r2_hidden(D_1471, '#skF_8'))), inference(resolution, [status(thm)], [c_123, c_10858])).
% 22.80/13.51  tff(c_18715, plain, (![D_1471, B_1472, C_1473]: (m1_subset_1('#skF_4'(D_1471, B_1472, C_1473), '#skF_6') | v1_xboole_0('#skF_6') | ~r2_hidden(D_1471, k2_zfmisc_1(B_1472, C_1473)) | ~r2_hidden(D_1471, '#skF_8'))), inference(resolution, [status(thm)], [c_18712, c_34])).
% 22.80/13.51  tff(c_92381, plain, (![D_6537, B_6538, C_6539]: (m1_subset_1('#skF_4'(D_6537, B_6538, C_6539), '#skF_6') | ~r2_hidden(D_6537, k2_zfmisc_1(B_6538, C_6539)) | ~r2_hidden(D_6537, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_9415, c_18715])).
% 22.80/13.51  tff(c_92815, plain, (![D_6543]: (m1_subset_1('#skF_4'(D_6543, '#skF_6', '#skF_7'), '#skF_6') | ~r2_hidden(D_6543, '#skF_8'))), inference(resolution, [status(thm)], [c_123, c_92381])).
% 22.80/13.51  tff(c_575, plain, (![D_49]: (D_49!='#skF_9' | ~m1_subset_1('#skF_5'(D_49, '#skF_6', '#skF_7'), '#skF_7') | ~m1_subset_1('#skF_4'(D_49, '#skF_6', '#skF_7'), '#skF_6') | ~r2_hidden(D_49, '#skF_8'))), inference(resolution, [status(thm)], [c_123, c_536])).
% 22.80/13.51  tff(c_93285, plain, (![D_6572]: (D_6572!='#skF_9' | ~m1_subset_1('#skF_5'(D_6572, '#skF_6', '#skF_7'), '#skF_7') | ~r2_hidden(D_6572, '#skF_8'))), inference(resolution, [status(thm)], [c_92815, c_575])).
% 22.80/13.51  tff(c_93388, plain, (![B_6573]: (B_6573!='#skF_9' | ~r2_hidden(B_6573, '#skF_8') | ~m1_subset_1(B_6573, '#skF_8'))), inference(resolution, [status(thm)], [c_92062, c_93285])).
% 22.80/13.51  tff(c_93631, plain, (~m1_subset_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_46, c_93388])).
% 22.80/13.51  tff(c_93752, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_93631])).
% 22.80/13.51  tff(c_93753, plain, (![B_855, C_856]: (~r2_hidden('#skF_1'('#skF_8'), k2_zfmisc_1(B_855, C_856)))), inference(splitRight, [status(thm)], [c_10954])).
% 22.80/13.51  tff(c_94161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93753, c_236])).
% 22.80/13.51  tff(c_94163, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_9414])).
% 22.80/13.51  tff(c_94162, plain, (v1_xboole_0('#skF_4'('#skF_1'('#skF_8'), '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_9414])).
% 22.80/13.51  tff(c_20, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_2'(A_5, B_6, C_7), B_6) | r2_hidden('#skF_3'(A_5, B_6, C_7), C_7) | k3_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 22.80/13.51  tff(c_885, plain, (![A_165, B_166, C_167]: (~r2_hidden('#skF_2'(A_165, B_166, C_167), C_167) | r2_hidden('#skF_3'(A_165, B_166, C_167), C_167) | k3_xboole_0(A_165, B_166)=C_167)), inference(cnfTransformation, [status(thm)], [f_40])).
% 22.80/13.51  tff(c_921, plain, (![A_168, B_169]: (r2_hidden('#skF_3'(A_168, B_169, B_169), B_169) | k3_xboole_0(A_168, B_169)=B_169)), inference(resolution, [status(thm)], [c_20, c_885])).
% 22.80/13.51  tff(c_952, plain, (![B_169, A_168]: (~v1_xboole_0(B_169) | k3_xboole_0(A_168, B_169)=B_169)), inference(resolution, [status(thm)], [c_921, c_2])).
% 22.80/13.51  tff(c_94191, plain, (![A_168]: (k3_xboole_0(A_168, '#skF_6')='#skF_6')), inference(resolution, [status(thm)], [c_94163, c_952])).
% 22.80/13.51  tff(c_663, plain, (![A_134, B_135, C_136]: (r2_hidden('#skF_2'(A_134, B_135, C_136), B_135) | r2_hidden('#skF_3'(A_134, B_135, C_136), C_136) | k3_xboole_0(A_134, B_135)=C_136)), inference(cnfTransformation, [status(thm)], [f_40])).
% 22.80/13.51  tff(c_840, plain, (![C_159, A_160, B_161]: (~v1_xboole_0(C_159) | r2_hidden('#skF_2'(A_160, B_161, C_159), B_161) | k3_xboole_0(A_160, B_161)=C_159)), inference(resolution, [status(thm)], [c_663, c_2])).
% 22.80/13.51  tff(c_871, plain, (![B_161, C_159, A_160]: (~v1_xboole_0(B_161) | ~v1_xboole_0(C_159) | k3_xboole_0(A_160, B_161)=C_159)), inference(resolution, [status(thm)], [c_840, c_2])).
% 22.80/13.51  tff(c_94192, plain, (![C_159, A_160]: (~v1_xboole_0(C_159) | k3_xboole_0(A_160, '#skF_6')=C_159)), inference(resolution, [status(thm)], [c_94163, c_871])).
% 22.80/13.51  tff(c_94524, plain, (![C_6591]: (~v1_xboole_0(C_6591) | C_6591='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_94191, c_94192])).
% 22.80/13.51  tff(c_94543, plain, ('#skF_4'('#skF_1'('#skF_8'), '#skF_6', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_94162, c_94524])).
% 22.80/13.51  tff(c_26, plain, (![A_13, B_14, C_15]: (k4_tarski('#skF_4'(A_13, B_14, C_15), '#skF_5'(A_13, B_14, C_15))=A_13 | ~r2_hidden(A_13, k2_zfmisc_1(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 22.80/13.51  tff(c_94572, plain, (k4_tarski('#skF_6', '#skF_5'('#skF_1'('#skF_8'), '#skF_6', '#skF_7'))='#skF_1'('#skF_8') | ~r2_hidden('#skF_1'('#skF_8'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_94543, c_26])).
% 22.80/13.51  tff(c_94583, plain, (k4_tarski('#skF_6', '#skF_5'('#skF_1'('#skF_8'), '#skF_6', '#skF_7'))='#skF_1'('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_236, c_94572])).
% 22.80/13.51  tff(c_168, plain, (![A_62, C_63, B_64, D_65]: (r2_hidden(A_62, C_63) | ~r2_hidden(k4_tarski(A_62, B_64), k2_zfmisc_1(C_63, D_65)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 22.80/13.51  tff(c_178, plain, (![A_66, B_67]: (r2_hidden(A_66, '#skF_6') | ~r2_hidden(k4_tarski(A_66, B_67), '#skF_8'))), inference(resolution, [status(thm)], [c_123, c_168])).
% 22.80/13.51  tff(c_181, plain, (![A_66, B_67]: (r2_hidden(A_66, '#skF_6') | ~m1_subset_1(k4_tarski(A_66, B_67), '#skF_8') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_36, c_178])).
% 22.80/13.51  tff(c_184, plain, (![A_66, B_67]: (r2_hidden(A_66, '#skF_6') | ~m1_subset_1(k4_tarski(A_66, B_67), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_51, c_181])).
% 22.80/13.51  tff(c_95833, plain, (r2_hidden('#skF_6', '#skF_6') | ~m1_subset_1('#skF_1'('#skF_8'), '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_94583, c_184])).
% 22.80/13.51  tff(c_95855, plain, (r2_hidden('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_95833])).
% 22.80/13.51  tff(c_95982, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_95855, c_2])).
% 22.80/13.51  tff(c_95990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94163, c_95982])).
% 22.80/13.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.80/13.51  
% 22.80/13.51  Inference rules
% 22.80/13.51  ----------------------
% 22.80/13.51  #Ref     : 0
% 22.80/13.51  #Sup     : 21913
% 22.80/13.51  #Fact    : 0
% 22.80/13.51  #Define  : 0
% 22.80/13.51  #Split   : 35
% 22.80/13.51  #Chain   : 0
% 22.80/13.51  #Close   : 0
% 22.80/13.51  
% 22.80/13.51  Ordering : KBO
% 22.80/13.51  
% 22.80/13.51  Simplification rules
% 22.80/13.51  ----------------------
% 22.80/13.51  #Subsume      : 6505
% 22.80/13.51  #Demod        : 8277
% 22.80/13.51  #Tautology    : 5299
% 22.80/13.51  #SimpNegUnit  : 697
% 22.80/13.51  #BackRed      : 428
% 22.80/13.51  
% 22.80/13.51  #Partial instantiations: 0
% 22.80/13.51  #Strategies tried      : 1
% 22.80/13.51  
% 22.80/13.51  Timing (in seconds)
% 22.80/13.51  ----------------------
% 22.80/13.51  Preprocessing        : 0.30
% 22.80/13.51  Parsing              : 0.16
% 22.80/13.52  CNF conversion       : 0.02
% 22.80/13.52  Main loop            : 12.43
% 22.80/13.52  Inferencing          : 2.85
% 22.80/13.52  Reduction            : 4.18
% 22.80/13.52  Demodulation         : 3.38
% 22.80/13.52  BG Simplification    : 0.27
% 22.80/13.52  Subsumption          : 4.19
% 22.80/13.52  Abstraction          : 0.38
% 22.80/13.52  MUC search           : 0.00
% 22.80/13.52  Cooper               : 0.00
% 22.80/13.52  Total                : 12.77
% 22.80/13.52  Index Insertion      : 0.00
% 22.80/13.52  Index Deletion       : 0.00
% 22.80/13.52  Index Matching       : 0.00
% 22.80/13.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
