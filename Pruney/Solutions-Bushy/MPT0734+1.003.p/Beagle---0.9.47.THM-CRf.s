%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0734+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:47 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 320 expanded)
%              Number of leaves         :   26 ( 122 expanded)
%              Depth                    :   12
%              Number of atoms          :  118 ( 880 expanded)
%              Number of equality atoms :   11 (  48 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v3_ordinal1 > v2_ordinal1 > v1_xboole_0 > v1_ordinal1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( v1_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ! [C] :
                ( v3_ordinal1(C)
               => ( ( r1_tarski(A,B)
                    & r2_hidden(B,C) )
                 => r2_hidden(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_ordinal1)).

tff(f_30,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_36,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_38,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_44,plain,(
    ! [A_28] :
      ( v1_ordinal1(A_28)
      | ~ v3_ordinal1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_51,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_44])).

tff(c_34,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_81,plain,(
    ! [B_41,A_42] :
      ( r1_tarski(B_41,A_42)
      | ~ r2_hidden(B_41,A_42)
      | ~ v1_ordinal1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_87,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_81])).

tff(c_91,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_87])).

tff(c_118,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_tarski(A_47,C_48)
      | ~ r1_tarski(B_49,C_48)
      | ~ r1_tarski(A_47,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_126,plain,(
    ! [A_51] :
      ( r1_tarski(A_51,'#skF_4')
      | ~ r1_tarski(A_51,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_91,c_118])).

tff(c_130,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_126])).

tff(c_42,plain,(
    v1_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_160,plain,(
    ! [A_62,B_63] :
      ( r2_hidden(A_62,B_63)
      | ~ r2_xboole_0(A_62,B_63)
      | ~ v3_ordinal1(B_63)
      | ~ v1_ordinal1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_525,plain,(
    ! [A_85,B_86] :
      ( r2_hidden(A_85,B_86)
      | ~ v3_ordinal1(B_86)
      | ~ v1_ordinal1(A_85)
      | B_86 = A_85
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(resolution,[status(thm)],[c_12,c_160])).

tff(c_32,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_536,plain,
    ( ~ v3_ordinal1('#skF_4')
    | ~ v1_ordinal1('#skF_2')
    | '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_525,c_32])).

tff(c_542,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_42,c_38,c_536])).

tff(c_62,plain,(
    ! [B_30,A_31] :
      ( ~ v1_xboole_0(B_30)
      | ~ r2_hidden(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_62])).

tff(c_92,plain,(
    ! [A_43,B_44] :
      ( r2_hidden(A_43,B_44)
      | v1_xboole_0(B_44)
      | ~ m1_subset_1(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_101,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_32])).

tff(c_106,plain,(
    ~ m1_subset_1('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_101])).

tff(c_552,plain,(
    ~ m1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_106])).

tff(c_554,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_36])).

tff(c_40,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_135,plain,(
    ! [A_53,C_54,B_55] :
      ( m1_subset_1(A_53,C_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(C_54))
      | ~ r2_hidden(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_138,plain,(
    ! [A_53,B_17,A_16] :
      ( m1_subset_1(A_53,B_17)
      | ~ r2_hidden(A_53,A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(resolution,[status(thm)],[c_26,c_135])).

tff(c_1404,plain,(
    ! [A_126,B_127,B_128] :
      ( m1_subset_1(A_126,B_127)
      | ~ r1_tarski(B_128,B_127)
      | ~ v3_ordinal1(B_128)
      | ~ v1_ordinal1(A_126)
      | B_128 = A_126
      | ~ r1_tarski(A_126,B_128) ) ),
    inference(resolution,[status(thm)],[c_525,c_138])).

tff(c_1432,plain,(
    ! [A_126] :
      ( m1_subset_1(A_126,'#skF_4')
      | ~ v3_ordinal1('#skF_3')
      | ~ v1_ordinal1(A_126)
      | A_126 = '#skF_3'
      | ~ r1_tarski(A_126,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_91,c_1404])).

tff(c_1459,plain,(
    ! [A_129] :
      ( m1_subset_1(A_129,'#skF_4')
      | ~ v1_ordinal1(A_129)
      | A_129 = '#skF_3'
      | ~ r1_tarski(A_129,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1432])).

tff(c_1486,plain,
    ( m1_subset_1('#skF_4','#skF_4')
    | ~ v1_ordinal1('#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_554,c_1459])).

tff(c_1509,plain,
    ( m1_subset_1('#skF_4','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_1486])).

tff(c_1510,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_552,c_1509])).

tff(c_139,plain,(
    ! [A_56,B_57,A_58] :
      ( m1_subset_1(A_56,B_57)
      | ~ r2_hidden(A_56,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(resolution,[status(thm)],[c_26,c_135])).

tff(c_148,plain,(
    ! [B_57] :
      ( m1_subset_1('#skF_3',B_57)
      | ~ r1_tarski('#skF_4',B_57) ) ),
    inference(resolution,[status(thm)],[c_34,c_139])).

tff(c_596,plain,(
    m1_subset_1('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_554,c_148])).

tff(c_1533,plain,(
    m1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1510,c_1510,c_596])).

tff(c_1549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_552,c_1533])).

%------------------------------------------------------------------------------
