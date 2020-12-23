%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:37 EST 2020

% Result     : Theorem 9.91s
% Output     : CNFRefutation 10.15s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 191 expanded)
%              Number of leaves         :   29 (  77 expanded)
%              Depth                    :   11
%              Number of atoms          :  186 ( 553 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k2_xboole_0 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( r1_tarski(C,k1_relat_1(k5_relat_1(A,B)))
              <=> ( r1_tarski(C,k1_relat_1(A))
                  & r1_tarski(k9_relat_1(A,C),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_40,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_56,plain,
    ( r1_tarski('#skF_6',k1_relat_1('#skF_4'))
    | r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_79,plain,(
    r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_14,plain,(
    ! [A_14,B_16] :
      ( k10_relat_1(A_14,k1_relat_1(B_16)) = k1_relat_1(k5_relat_1(A_14,B_16))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_12,plain,(
    ! [C_13,A_11,B_12] :
      ( r1_tarski(k9_relat_1(C_13,A_11),k9_relat_1(C_13,B_12))
      | ~ r1_tarski(A_11,B_12)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_291,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(k9_relat_1(B_67,k10_relat_1(B_67,A_68)),A_68)
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_295,plain,(
    ! [B_67,A_68] :
      ( k2_xboole_0(k9_relat_1(B_67,k10_relat_1(B_67,A_68)),A_68) = A_68
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_291,c_10])).

tff(c_59,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_1'(A_42,B_43),A_42)
      | r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,(
    ! [A_42] : r1_tarski(A_42,A_42) ),
    inference(resolution,[status(thm)],[c_59,c_4])).

tff(c_84,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_tarski(A_46,C_47)
      | ~ r1_tarski(k2_xboole_0(A_46,B_48),C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_92,plain,(
    ! [A_46,B_48] : r1_tarski(A_46,k2_xboole_0(A_46,B_48)) ),
    inference(resolution,[status(thm)],[c_64,c_84])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_163,plain,(
    ! [C_56,B_57,A_58] :
      ( r2_hidden(C_56,B_57)
      | ~ r2_hidden(C_56,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_296,plain,(
    ! [A_69,B_70,B_71] :
      ( r2_hidden('#skF_1'(A_69,B_70),B_71)
      | ~ r1_tarski(A_69,B_71)
      | r1_tarski(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_163])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6996,plain,(
    ! [A_451,B_452,B_453,B_454] :
      ( r2_hidden('#skF_1'(A_451,B_452),B_453)
      | ~ r1_tarski(B_454,B_453)
      | ~ r1_tarski(A_451,B_454)
      | r1_tarski(A_451,B_452) ) ),
    inference(resolution,[status(thm)],[c_296,c_2])).

tff(c_8028,plain,(
    ! [A_498,B_499,A_500,B_501] :
      ( r2_hidden('#skF_1'(A_498,B_499),k2_xboole_0(A_500,B_501))
      | ~ r1_tarski(A_498,A_500)
      | r1_tarski(A_498,B_499) ) ),
    inference(resolution,[status(thm)],[c_92,c_6996])).

tff(c_8075,plain,(
    ! [A_505,A_506,B_507] :
      ( ~ r1_tarski(A_505,A_506)
      | r1_tarski(A_505,k2_xboole_0(A_506,B_507)) ) ),
    inference(resolution,[status(thm)],[c_8028,c_4])).

tff(c_15402,plain,(
    ! [A_789,B_790,A_791] :
      ( ~ r1_tarski(A_789,k9_relat_1(B_790,k10_relat_1(B_790,A_791)))
      | r1_tarski(A_789,A_791)
      | ~ v1_funct_1(B_790)
      | ~ v1_relat_1(B_790) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_8075])).

tff(c_15869,plain,(
    ! [C_800,A_801,A_802] :
      ( r1_tarski(k9_relat_1(C_800,A_801),A_802)
      | ~ v1_funct_1(C_800)
      | ~ r1_tarski(A_801,k10_relat_1(C_800,A_802))
      | ~ v1_relat_1(C_800) ) ),
    inference(resolution,[status(thm)],[c_12,c_15402])).

tff(c_1007,plain,(
    ! [A_125,B_126,B_127,B_128] :
      ( r2_hidden('#skF_1'(A_125,B_126),B_127)
      | ~ r1_tarski(B_128,B_127)
      | ~ r1_tarski(A_125,B_128)
      | r1_tarski(A_125,B_126) ) ),
    inference(resolution,[status(thm)],[c_296,c_2])).

tff(c_1048,plain,(
    ! [A_125,B_126] :
      ( r2_hidden('#skF_1'(A_125,B_126),k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
      | ~ r1_tarski(A_125,'#skF_7')
      | r1_tarski(A_125,B_126) ) ),
    inference(resolution,[status(thm)],[c_79,c_1007])).

tff(c_621,plain,(
    ! [D_93,A_94,B_95] :
      ( r2_hidden(D_93,k1_relat_1(A_94))
      | ~ r2_hidden(D_93,k10_relat_1(A_94,B_95))
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_5620,plain,(
    ! [D_376,A_377,B_378] :
      ( r2_hidden(D_376,k1_relat_1(A_377))
      | ~ r2_hidden(D_376,k1_relat_1(k5_relat_1(A_377,B_378)))
      | ~ v1_funct_1(A_377)
      | ~ v1_relat_1(A_377)
      | ~ v1_relat_1(B_378)
      | ~ v1_relat_1(A_377) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_621])).

tff(c_5654,plain,(
    ! [A_125,B_126] :
      ( r2_hidden('#skF_1'(A_125,B_126),k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(A_125,'#skF_7')
      | r1_tarski(A_125,B_126) ) ),
    inference(resolution,[status(thm)],[c_1048,c_5620])).

tff(c_5683,plain,(
    ! [A_379,B_380] :
      ( r2_hidden('#skF_1'(A_379,B_380),k1_relat_1('#skF_4'))
      | ~ r1_tarski(A_379,'#skF_7')
      | r1_tarski(A_379,B_380) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_42,c_5654])).

tff(c_5692,plain,(
    ! [A_381] :
      ( ~ r1_tarski(A_381,'#skF_7')
      | r1_tarski(A_381,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_5683,c_4])).

tff(c_50,plain,
    ( r1_tarski('#skF_6',k1_relat_1('#skF_4'))
    | ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5'))
    | ~ r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_379,plain,(
    ~ r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_5800,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_5692,c_379])).

tff(c_5855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5800])).

tff(c_5857,plain,(
    r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_46,plain,
    ( ~ r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5'))
    | ~ r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_5863,plain,
    ( ~ r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5857,c_46])).

tff(c_5864,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_5863])).

tff(c_15904,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ r1_tarski('#skF_7',k10_relat_1('#skF_4',k1_relat_1('#skF_5')))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_15869,c_5864])).

tff(c_15923,plain,(
    ~ r1_tarski('#skF_7',k10_relat_1('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_15904])).

tff(c_15963,plain,
    ( ~ r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_15923])).

tff(c_15966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_79,c_15963])).

tff(c_15967,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_5863])).

tff(c_15968,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_5863])).

tff(c_5856,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5'))
    | r1_tarski('#skF_6',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_16095,plain,(
    r1_tarski('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15968,c_5856])).

tff(c_48,plain,
    ( r1_tarski(k9_relat_1('#skF_4','#skF_6'),k1_relat_1('#skF_5'))
    | ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5'))
    | ~ r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_15974,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5857,c_15968,c_48])).

tff(c_16881,plain,(
    ! [A_848,C_849,B_850] :
      ( r1_tarski(A_848,k10_relat_1(C_849,B_850))
      | ~ r1_tarski(k9_relat_1(C_849,A_848),B_850)
      | ~ r1_tarski(A_848,k1_relat_1(C_849))
      | ~ v1_funct_1(C_849)
      | ~ v1_relat_1(C_849) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_16902,plain,
    ( r1_tarski('#skF_6',k10_relat_1('#skF_4',k1_relat_1('#skF_5')))
    | ~ r1_tarski('#skF_6',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_15974,c_16881])).

tff(c_16952,plain,(
    r1_tarski('#skF_6',k10_relat_1('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_16095,c_16902])).

tff(c_16969,plain,
    ( r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_16952])).

tff(c_16972,plain,(
    r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_16969])).

tff(c_16974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15967,c_16972])).

tff(c_16976,plain,(
    ~ r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_52,plain,
    ( ~ r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_17138,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_16976,c_52])).

tff(c_16975,plain,(
    r1_tarski('#skF_6',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,
    ( r1_tarski(k9_relat_1('#skF_4','#skF_6'),k1_relat_1('#skF_5'))
    | r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_16981,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_16976,c_54])).

tff(c_18412,plain,(
    ! [A_949,C_950,B_951] :
      ( r1_tarski(A_949,k10_relat_1(C_950,B_951))
      | ~ r1_tarski(k9_relat_1(C_950,A_949),B_951)
      | ~ r1_tarski(A_949,k1_relat_1(C_950))
      | ~ v1_funct_1(C_950)
      | ~ v1_relat_1(C_950) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_18459,plain,
    ( r1_tarski('#skF_6',k10_relat_1('#skF_4',k1_relat_1('#skF_5')))
    | ~ r1_tarski('#skF_6',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16981,c_18412])).

tff(c_18488,plain,(
    r1_tarski('#skF_6',k10_relat_1('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_16975,c_18459])).

tff(c_18495,plain,
    ( r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_18488])).

tff(c_18498,plain,(
    r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_18495])).

tff(c_18500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17138,c_18498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:49:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.91/3.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.91/3.85  
% 9.91/3.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.91/3.85  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k2_xboole_0 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 9.91/3.85  
% 9.91/3.85  %Foreground sorts:
% 9.91/3.85  
% 9.91/3.85  
% 9.91/3.85  %Background operators:
% 9.91/3.85  
% 9.91/3.85  
% 9.91/3.85  %Foreground operators:
% 9.91/3.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.91/3.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.91/3.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.91/3.85  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.91/3.85  tff('#skF_7', type, '#skF_7': $i).
% 9.91/3.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.91/3.85  tff('#skF_5', type, '#skF_5': $i).
% 9.91/3.85  tff('#skF_6', type, '#skF_6': $i).
% 9.91/3.85  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.91/3.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.91/3.85  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.91/3.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.91/3.85  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.91/3.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.91/3.85  tff('#skF_4', type, '#skF_4': $i).
% 9.91/3.85  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.91/3.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.91/3.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.91/3.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.91/3.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.91/3.85  
% 10.15/3.87  tff(f_100, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_1)).
% 10.15/3.87  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 10.15/3.87  tff(f_46, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 10.15/3.87  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 10.15/3.87  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.15/3.87  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.15/3.87  tff(f_36, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 10.15/3.87  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 10.15/3.87  tff(f_83, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 10.15/3.87  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.15/3.87  tff(c_40, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.15/3.87  tff(c_56, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_4')) | r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.15/3.87  tff(c_79, plain, (r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_56])).
% 10.15/3.87  tff(c_14, plain, (![A_14, B_16]: (k10_relat_1(A_14, k1_relat_1(B_16))=k1_relat_1(k5_relat_1(A_14, B_16)) | ~v1_relat_1(B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.15/3.87  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.15/3.87  tff(c_12, plain, (![C_13, A_11, B_12]: (r1_tarski(k9_relat_1(C_13, A_11), k9_relat_1(C_13, B_12)) | ~r1_tarski(A_11, B_12) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.15/3.87  tff(c_291, plain, (![B_67, A_68]: (r1_tarski(k9_relat_1(B_67, k10_relat_1(B_67, A_68)), A_68) | ~v1_funct_1(B_67) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.15/3.87  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.15/3.87  tff(c_295, plain, (![B_67, A_68]: (k2_xboole_0(k9_relat_1(B_67, k10_relat_1(B_67, A_68)), A_68)=A_68 | ~v1_funct_1(B_67) | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_291, c_10])).
% 10.15/3.87  tff(c_59, plain, (![A_42, B_43]: (r2_hidden('#skF_1'(A_42, B_43), A_42) | r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.15/3.87  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.15/3.87  tff(c_64, plain, (![A_42]: (r1_tarski(A_42, A_42))), inference(resolution, [status(thm)], [c_59, c_4])).
% 10.15/3.87  tff(c_84, plain, (![A_46, C_47, B_48]: (r1_tarski(A_46, C_47) | ~r1_tarski(k2_xboole_0(A_46, B_48), C_47))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.15/3.87  tff(c_92, plain, (![A_46, B_48]: (r1_tarski(A_46, k2_xboole_0(A_46, B_48)))), inference(resolution, [status(thm)], [c_64, c_84])).
% 10.15/3.87  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.15/3.87  tff(c_163, plain, (![C_56, B_57, A_58]: (r2_hidden(C_56, B_57) | ~r2_hidden(C_56, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.15/3.87  tff(c_296, plain, (![A_69, B_70, B_71]: (r2_hidden('#skF_1'(A_69, B_70), B_71) | ~r1_tarski(A_69, B_71) | r1_tarski(A_69, B_70))), inference(resolution, [status(thm)], [c_6, c_163])).
% 10.15/3.87  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.15/3.87  tff(c_6996, plain, (![A_451, B_452, B_453, B_454]: (r2_hidden('#skF_1'(A_451, B_452), B_453) | ~r1_tarski(B_454, B_453) | ~r1_tarski(A_451, B_454) | r1_tarski(A_451, B_452))), inference(resolution, [status(thm)], [c_296, c_2])).
% 10.15/3.87  tff(c_8028, plain, (![A_498, B_499, A_500, B_501]: (r2_hidden('#skF_1'(A_498, B_499), k2_xboole_0(A_500, B_501)) | ~r1_tarski(A_498, A_500) | r1_tarski(A_498, B_499))), inference(resolution, [status(thm)], [c_92, c_6996])).
% 10.15/3.87  tff(c_8075, plain, (![A_505, A_506, B_507]: (~r1_tarski(A_505, A_506) | r1_tarski(A_505, k2_xboole_0(A_506, B_507)))), inference(resolution, [status(thm)], [c_8028, c_4])).
% 10.15/3.87  tff(c_15402, plain, (![A_789, B_790, A_791]: (~r1_tarski(A_789, k9_relat_1(B_790, k10_relat_1(B_790, A_791))) | r1_tarski(A_789, A_791) | ~v1_funct_1(B_790) | ~v1_relat_1(B_790))), inference(superposition, [status(thm), theory('equality')], [c_295, c_8075])).
% 10.15/3.87  tff(c_15869, plain, (![C_800, A_801, A_802]: (r1_tarski(k9_relat_1(C_800, A_801), A_802) | ~v1_funct_1(C_800) | ~r1_tarski(A_801, k10_relat_1(C_800, A_802)) | ~v1_relat_1(C_800))), inference(resolution, [status(thm)], [c_12, c_15402])).
% 10.15/3.87  tff(c_1007, plain, (![A_125, B_126, B_127, B_128]: (r2_hidden('#skF_1'(A_125, B_126), B_127) | ~r1_tarski(B_128, B_127) | ~r1_tarski(A_125, B_128) | r1_tarski(A_125, B_126))), inference(resolution, [status(thm)], [c_296, c_2])).
% 10.15/3.87  tff(c_1048, plain, (![A_125, B_126]: (r2_hidden('#skF_1'(A_125, B_126), k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~r1_tarski(A_125, '#skF_7') | r1_tarski(A_125, B_126))), inference(resolution, [status(thm)], [c_79, c_1007])).
% 10.15/3.87  tff(c_621, plain, (![D_93, A_94, B_95]: (r2_hidden(D_93, k1_relat_1(A_94)) | ~r2_hidden(D_93, k10_relat_1(A_94, B_95)) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.15/3.87  tff(c_5620, plain, (![D_376, A_377, B_378]: (r2_hidden(D_376, k1_relat_1(A_377)) | ~r2_hidden(D_376, k1_relat_1(k5_relat_1(A_377, B_378))) | ~v1_funct_1(A_377) | ~v1_relat_1(A_377) | ~v1_relat_1(B_378) | ~v1_relat_1(A_377))), inference(superposition, [status(thm), theory('equality')], [c_14, c_621])).
% 10.15/3.87  tff(c_5654, plain, (![A_125, B_126]: (r2_hidden('#skF_1'(A_125, B_126), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4') | ~r1_tarski(A_125, '#skF_7') | r1_tarski(A_125, B_126))), inference(resolution, [status(thm)], [c_1048, c_5620])).
% 10.15/3.87  tff(c_5683, plain, (![A_379, B_380]: (r2_hidden('#skF_1'(A_379, B_380), k1_relat_1('#skF_4')) | ~r1_tarski(A_379, '#skF_7') | r1_tarski(A_379, B_380))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_42, c_5654])).
% 10.15/3.87  tff(c_5692, plain, (![A_381]: (~r1_tarski(A_381, '#skF_7') | r1_tarski(A_381, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_5683, c_4])).
% 10.15/3.87  tff(c_50, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_4')) | ~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5')) | ~r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.15/3.87  tff(c_379, plain, (~r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_50])).
% 10.15/3.87  tff(c_5800, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_5692, c_379])).
% 10.15/3.87  tff(c_5855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_5800])).
% 10.15/3.87  tff(c_5857, plain, (r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_50])).
% 10.15/3.87  tff(c_46, plain, (~r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5')) | ~r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.15/3.87  tff(c_5863, plain, (~r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5857, c_46])).
% 10.15/3.87  tff(c_5864, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_5863])).
% 10.15/3.87  tff(c_15904, plain, (~v1_funct_1('#skF_4') | ~r1_tarski('#skF_7', k10_relat_1('#skF_4', k1_relat_1('#skF_5'))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_15869, c_5864])).
% 10.15/3.87  tff(c_15923, plain, (~r1_tarski('#skF_7', k10_relat_1('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_15904])).
% 10.15/3.87  tff(c_15963, plain, (~r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14, c_15923])).
% 10.15/3.87  tff(c_15966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_79, c_15963])).
% 10.15/3.87  tff(c_15967, plain, (~r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_5863])).
% 10.15/3.87  tff(c_15968, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_5863])).
% 10.15/3.87  tff(c_5856, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5')) | r1_tarski('#skF_6', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_50])).
% 10.15/3.87  tff(c_16095, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15968, c_5856])).
% 10.15/3.87  tff(c_48, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5')) | ~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5')) | ~r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.15/3.87  tff(c_15974, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5857, c_15968, c_48])).
% 10.15/3.87  tff(c_16881, plain, (![A_848, C_849, B_850]: (r1_tarski(A_848, k10_relat_1(C_849, B_850)) | ~r1_tarski(k9_relat_1(C_849, A_848), B_850) | ~r1_tarski(A_848, k1_relat_1(C_849)) | ~v1_funct_1(C_849) | ~v1_relat_1(C_849))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.15/3.87  tff(c_16902, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_4', k1_relat_1('#skF_5'))) | ~r1_tarski('#skF_6', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_15974, c_16881])).
% 10.15/3.87  tff(c_16952, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_16095, c_16902])).
% 10.15/3.87  tff(c_16969, plain, (r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14, c_16952])).
% 10.15/3.87  tff(c_16972, plain, (r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_16969])).
% 10.15/3.87  tff(c_16974, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15967, c_16972])).
% 10.15/3.87  tff(c_16976, plain, (~r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_56])).
% 10.15/3.87  tff(c_52, plain, (~r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.15/3.87  tff(c_17138, plain, (~r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_16976, c_52])).
% 10.15/3.87  tff(c_16975, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_56])).
% 10.15/3.87  tff(c_54, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5')) | r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.15/3.87  tff(c_16981, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_16976, c_54])).
% 10.15/3.87  tff(c_18412, plain, (![A_949, C_950, B_951]: (r1_tarski(A_949, k10_relat_1(C_950, B_951)) | ~r1_tarski(k9_relat_1(C_950, A_949), B_951) | ~r1_tarski(A_949, k1_relat_1(C_950)) | ~v1_funct_1(C_950) | ~v1_relat_1(C_950))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.15/3.87  tff(c_18459, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_4', k1_relat_1('#skF_5'))) | ~r1_tarski('#skF_6', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16981, c_18412])).
% 10.15/3.87  tff(c_18488, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_16975, c_18459])).
% 10.15/3.87  tff(c_18495, plain, (r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14, c_18488])).
% 10.15/3.87  tff(c_18498, plain, (r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_18495])).
% 10.15/3.87  tff(c_18500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17138, c_18498])).
% 10.15/3.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.15/3.87  
% 10.15/3.87  Inference rules
% 10.15/3.87  ----------------------
% 10.15/3.87  #Ref     : 0
% 10.15/3.87  #Sup     : 4736
% 10.15/3.87  #Fact    : 0
% 10.15/3.87  #Define  : 0
% 10.15/3.87  #Split   : 3
% 10.15/3.87  #Chain   : 0
% 10.15/3.87  #Close   : 0
% 10.15/3.87  
% 10.15/3.87  Ordering : KBO
% 10.15/3.87  
% 10.15/3.87  Simplification rules
% 10.15/3.87  ----------------------
% 10.15/3.87  #Subsume      : 984
% 10.15/3.87  #Demod        : 1118
% 10.15/3.87  #Tautology    : 1058
% 10.15/3.87  #SimpNegUnit  : 6
% 10.15/3.87  #BackRed      : 0
% 10.15/3.87  
% 10.15/3.87  #Partial instantiations: 0
% 10.15/3.87  #Strategies tried      : 1
% 10.15/3.87  
% 10.15/3.87  Timing (in seconds)
% 10.15/3.87  ----------------------
% 10.15/3.87  Preprocessing        : 0.38
% 10.15/3.87  Parsing              : 0.18
% 10.15/3.87  CNF conversion       : 0.03
% 10.15/3.87  Main loop            : 2.70
% 10.15/3.87  Inferencing          : 0.62
% 10.15/3.87  Reduction            : 0.84
% 10.15/3.87  Demodulation         : 0.65
% 10.15/3.87  BG Simplification    : 0.09
% 10.15/3.87  Subsumption          : 0.96
% 10.15/3.87  Abstraction          : 0.10
% 10.15/3.87  MUC search           : 0.00
% 10.15/3.87  Cooper               : 0.00
% 10.15/3.87  Total                : 3.11
% 10.15/3.87  Index Insertion      : 0.00
% 10.15/3.87  Index Deletion       : 0.00
% 10.15/3.87  Index Matching       : 0.00
% 10.15/3.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
