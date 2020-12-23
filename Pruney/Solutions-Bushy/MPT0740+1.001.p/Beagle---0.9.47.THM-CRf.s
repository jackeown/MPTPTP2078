%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0740+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:47 EST 2020

% Result     : Theorem 45.77s
% Output     : CNFRefutation 45.77s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 133 expanded)
%              Number of leaves         :   32 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  163 ( 298 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v3_ordinal1 > v2_ordinal1 > v1_xboole_0 > v1_ordinal1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_6 > #skF_2 > #skF_1 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,axiom,(
    ! [A] :
      ( v2_ordinal1(A)
    <=> ! [B,C] :
          ~ ( r2_hidden(B,A)
            & r2_hidden(C,A)
            & ~ r2_hidden(B,C)
            & B != C
            & ~ r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_ordinal1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_112,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_60,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
    <=> ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_ordinal1)).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => v3_ordinal1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_ordinal1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_97,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_116,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_91,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(c_18025,plain,(
    ! [A_707] :
      ( '#skF_2'(A_707) != '#skF_3'(A_707)
      | v2_ordinal1(A_707) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | v1_ordinal1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_257,plain,(
    ! [A_95,C_96] :
      ( r2_hidden('#skF_7'(A_95,k3_tarski(A_95),C_96),A_95)
      | ~ r2_hidden(C_96,k3_tarski(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_60,plain,(
    ! [B_46,A_45] :
      ( ~ v1_xboole_0(B_46)
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_276,plain,(
    ! [A_97,C_98] :
      ( ~ v1_xboole_0(A_97)
      | ~ r2_hidden(C_98,k3_tarski(A_97)) ) ),
    inference(resolution,[status(thm)],[c_257,c_60])).

tff(c_303,plain,(
    ! [A_100] :
      ( ~ v1_xboole_0(A_100)
      | v1_ordinal1(k3_tarski(A_100)) ) ),
    inference(resolution,[status(thm)],[c_10,c_276])).

tff(c_78,plain,(
    ! [A_53] :
      ( v3_ordinal1(A_53)
      | ~ v2_ordinal1(A_53)
      | ~ v1_ordinal1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_64,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_90,plain,
    ( ~ v2_ordinal1(k3_tarski('#skF_8'))
    | ~ v1_ordinal1(k3_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_78,c_64])).

tff(c_96,plain,(
    ~ v1_ordinal1(k3_tarski('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_307,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_303,c_96])).

tff(c_66,plain,(
    v3_ordinal1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_67,plain,(
    ! [A_49] :
      ( v1_ordinal1(A_49)
      | ~ v3_ordinal1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_71,plain,(
    v1_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_67])).

tff(c_6,plain,(
    ! [B_5,A_2] :
      ( r1_tarski(B_5,A_2)
      | ~ r2_hidden(B_5,A_2)
      | ~ v1_ordinal1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_273,plain,(
    ! [A_95,C_96] :
      ( r1_tarski('#skF_7'(A_95,k3_tarski(A_95),C_96),A_95)
      | ~ v1_ordinal1(A_95)
      | ~ r2_hidden(C_96,k3_tarski(A_95)) ) ),
    inference(resolution,[status(thm)],[c_257,c_6])).

tff(c_336,plain,(
    ! [C_105,A_106] :
      ( r2_hidden(C_105,'#skF_7'(A_106,k3_tarski(A_106),C_105))
      | ~ r2_hidden(C_105,k3_tarski(A_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_56,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(A_40,k1_zfmisc_1(B_41))
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_193,plain,(
    ! [A_81,C_82,B_83] :
      ( m1_subset_1(A_81,C_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(C_82))
      | ~ r2_hidden(A_81,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_196,plain,(
    ! [A_81,B_41,A_40] :
      ( m1_subset_1(A_81,B_41)
      | ~ r2_hidden(A_81,A_40)
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_56,c_193])).

tff(c_17387,plain,(
    ! [C_693,B_694,A_695] :
      ( m1_subset_1(C_693,B_694)
      | ~ r1_tarski('#skF_7'(A_695,k3_tarski(A_695),C_693),B_694)
      | ~ r2_hidden(C_693,k3_tarski(A_695)) ) ),
    inference(resolution,[status(thm)],[c_336,c_196])).

tff(c_17436,plain,(
    ! [C_696,A_697] :
      ( m1_subset_1(C_696,A_697)
      | ~ v1_ordinal1(A_697)
      | ~ r2_hidden(C_696,k3_tarski(A_697)) ) ),
    inference(resolution,[status(thm)],[c_273,c_17387])).

tff(c_17812,plain,(
    ! [A_700] :
      ( m1_subset_1('#skF_1'(k3_tarski(A_700)),A_700)
      | ~ v1_ordinal1(A_700)
      | v1_ordinal1(k3_tarski(A_700)) ) ),
    inference(resolution,[status(thm)],[c_10,c_17436])).

tff(c_52,plain,(
    ! [A_38,B_39] :
      ( r2_hidden(A_38,B_39)
      | v1_xboole_0(B_39)
      | ~ m1_subset_1(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_119,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(A_67,k3_tarski(B_68))
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_8,plain,(
    ! [A_2] :
      ( ~ r1_tarski('#skF_1'(A_2),A_2)
      | v1_ordinal1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_185,plain,(
    ! [B_78] :
      ( v1_ordinal1(k3_tarski(B_78))
      | ~ r2_hidden('#skF_1'(k3_tarski(B_78)),B_78) ) ),
    inference(resolution,[status(thm)],[c_119,c_8])).

tff(c_190,plain,(
    ! [B_39] :
      ( v1_ordinal1(k3_tarski(B_39))
      | v1_xboole_0(B_39)
      | ~ m1_subset_1('#skF_1'(k3_tarski(B_39)),B_39) ) ),
    inference(resolution,[status(thm)],[c_52,c_185])).

tff(c_17979,plain,(
    ! [A_703] :
      ( v1_xboole_0(A_703)
      | ~ v1_ordinal1(A_703)
      | v1_ordinal1(k3_tarski(A_703)) ) ),
    inference(resolution,[status(thm)],[c_17812,c_190])).

tff(c_17982,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_17979,c_96])).

tff(c_18009,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_17982])).

tff(c_18011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_18009])).

tff(c_18012,plain,(
    ~ v2_ordinal1(k3_tarski('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_18029,plain,(
    '#skF_2'(k3_tarski('#skF_8')) != '#skF_3'(k3_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_18025,c_18012])).

tff(c_20,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_3'(A_6),A_6)
      | v2_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18127,plain,(
    ! [A_735,C_736] :
      ( r2_hidden('#skF_7'(A_735,k3_tarski(A_735),C_736),A_735)
      | ~ r2_hidden(C_736,k3_tarski(A_735)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_48,plain,(
    ! [A_33,B_34] :
      ( v3_ordinal1(A_33)
      | ~ r2_hidden(A_33,B_34)
      | ~ v3_ordinal1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18141,plain,(
    ! [A_735,C_736] :
      ( v3_ordinal1('#skF_7'(A_735,k3_tarski(A_735),C_736))
      | ~ v3_ordinal1(A_735)
      | ~ r2_hidden(C_736,k3_tarski(A_735)) ) ),
    inference(resolution,[status(thm)],[c_18127,c_48])).

tff(c_18203,plain,(
    ! [C_745,A_746] :
      ( r2_hidden(C_745,'#skF_7'(A_746,k3_tarski(A_746),C_745))
      | ~ r2_hidden(C_745,k3_tarski(A_746)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20484,plain,(
    ! [C_921,A_922] :
      ( v3_ordinal1(C_921)
      | ~ v3_ordinal1('#skF_7'(A_922,k3_tarski(A_922),C_921))
      | ~ r2_hidden(C_921,k3_tarski(A_922)) ) ),
    inference(resolution,[status(thm)],[c_18203,c_48])).

tff(c_20493,plain,(
    ! [C_923,A_924] :
      ( v3_ordinal1(C_923)
      | ~ v3_ordinal1(A_924)
      | ~ r2_hidden(C_923,k3_tarski(A_924)) ) ),
    inference(resolution,[status(thm)],[c_18141,c_20484])).

tff(c_20580,plain,(
    ! [A_924] :
      ( v3_ordinal1('#skF_3'(k3_tarski(A_924)))
      | ~ v3_ordinal1(A_924)
      | v2_ordinal1(k3_tarski(A_924)) ) ),
    inference(resolution,[status(thm)],[c_20,c_20493])).

tff(c_22,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | v2_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20579,plain,(
    ! [A_924] :
      ( v3_ordinal1('#skF_2'(k3_tarski(A_924)))
      | ~ v3_ordinal1(A_924)
      | v2_ordinal1(k3_tarski(A_924)) ) ),
    inference(resolution,[status(thm)],[c_22,c_20493])).

tff(c_18263,plain,(
    ! [B_751,A_752] :
      ( r2_hidden(B_751,A_752)
      | B_751 = A_752
      | r2_hidden(A_752,B_751)
      | ~ v3_ordinal1(B_751)
      | ~ v3_ordinal1(A_752) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_18,plain,(
    ! [A_6] :
      ( ~ r2_hidden('#skF_2'(A_6),'#skF_3'(A_6))
      | v2_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_27944,plain,(
    ! [A_1157] :
      ( v2_ordinal1(A_1157)
      | '#skF_2'(A_1157) = '#skF_3'(A_1157)
      | r2_hidden('#skF_3'(A_1157),'#skF_2'(A_1157))
      | ~ v3_ordinal1('#skF_2'(A_1157))
      | ~ v3_ordinal1('#skF_3'(A_1157)) ) ),
    inference(resolution,[status(thm)],[c_18263,c_18])).

tff(c_14,plain,(
    ! [A_6] :
      ( ~ r2_hidden('#skF_3'(A_6),'#skF_2'(A_6))
      | v2_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_27988,plain,(
    ! [A_1158] :
      ( v2_ordinal1(A_1158)
      | '#skF_2'(A_1158) = '#skF_3'(A_1158)
      | ~ v3_ordinal1('#skF_2'(A_1158))
      | ~ v3_ordinal1('#skF_3'(A_1158)) ) ),
    inference(resolution,[status(thm)],[c_27944,c_14])).

tff(c_127331,plain,(
    ! [A_2241] :
      ( '#skF_2'(k3_tarski(A_2241)) = '#skF_3'(k3_tarski(A_2241))
      | ~ v3_ordinal1('#skF_3'(k3_tarski(A_2241)))
      | ~ v3_ordinal1(A_2241)
      | v2_ordinal1(k3_tarski(A_2241)) ) ),
    inference(resolution,[status(thm)],[c_20579,c_27988])).

tff(c_127416,plain,(
    ! [A_2242] :
      ( '#skF_2'(k3_tarski(A_2242)) = '#skF_3'(k3_tarski(A_2242))
      | ~ v3_ordinal1(A_2242)
      | v2_ordinal1(k3_tarski(A_2242)) ) ),
    inference(resolution,[status(thm)],[c_20580,c_127331])).

tff(c_127419,plain,
    ( '#skF_2'(k3_tarski('#skF_8')) = '#skF_3'(k3_tarski('#skF_8'))
    | ~ v3_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_127416,c_18012])).

tff(c_127494,plain,(
    '#skF_2'(k3_tarski('#skF_8')) = '#skF_3'(k3_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_127419])).

tff(c_127496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18029,c_127494])).

%------------------------------------------------------------------------------
