%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:28 EST 2020

% Result     : Theorem 54.26s
% Output     : CNFRefutation 54.26s
% Verified   : 
% Statistics : Number of formulae       :  101 (1247 expanded)
%              Number of leaves         :   29 ( 433 expanded)
%              Depth                    :   15
%              Number of atoms          :  174 (3410 expanded)
%              Number of equality atoms :   43 ( 988 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k4_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( B = k4_relat_1(A)
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),B)
              <=> r2_hidden(k4_tarski(D,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_46,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(c_50,plain,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_62,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_66,plain,(
    ! [A_14] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_14) ) ),
    inference(resolution,[status(thm)],[c_30,c_62])).

tff(c_68,plain,(
    ! [A_14] : ~ v1_relat_1(A_14) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_48,plain,(
    ! [A_38,B_39,C_40,D_41] : v1_relat_1(k2_tarski(k4_tarski(A_38,B_39),k4_tarski(C_40,D_41))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_71,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_48])).

tff(c_72,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_26,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_936,plain,(
    ! [A_163,B_164] :
      ( r2_hidden(k4_tarski('#skF_5'(A_163,B_164),'#skF_4'(A_163,B_164)),A_163)
      | r2_hidden(k4_tarski('#skF_6'(A_163,B_164),'#skF_7'(A_163,B_164)),B_164)
      | k4_relat_1(A_163) = B_164
      | ~ v1_relat_1(B_164)
      | ~ v1_relat_1(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_13032,plain,(
    ! [A_534,B_535,B_536] :
      ( r2_hidden(k4_tarski('#skF_5'(A_534,B_535),'#skF_4'(A_534,B_535)),B_536)
      | ~ r1_tarski(A_534,B_536)
      | r2_hidden(k4_tarski('#skF_6'(A_534,B_535),'#skF_7'(A_534,B_535)),B_535)
      | k4_relat_1(A_534) = B_535
      | ~ v1_relat_1(B_535)
      | ~ v1_relat_1(A_534) ) ),
    inference(resolution,[status(thm)],[c_936,c_2])).

tff(c_13145,plain,(
    ! [A_534,B_535,B_2,B_536] :
      ( r2_hidden(k4_tarski('#skF_6'(A_534,B_535),'#skF_7'(A_534,B_535)),B_2)
      | ~ r1_tarski(B_535,B_2)
      | r2_hidden(k4_tarski('#skF_5'(A_534,B_535),'#skF_4'(A_534,B_535)),B_536)
      | ~ r1_tarski(A_534,B_536)
      | k4_relat_1(A_534) = B_535
      | ~ v1_relat_1(B_535)
      | ~ v1_relat_1(A_534) ) ),
    inference(resolution,[status(thm)],[c_13032,c_2])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_469,plain,(
    ! [A_119,B_120,C_121] :
      ( ~ r2_hidden('#skF_2'(A_119,B_120,C_121),C_121)
      | r2_hidden('#skF_3'(A_119,B_120,C_121),C_121)
      | k4_xboole_0(A_119,B_120) = C_121 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_478,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7,A_6),A_6)
      | k4_xboole_0(A_6,B_7) = A_6 ) ),
    inference(resolution,[status(thm)],[c_24,c_469])).

tff(c_480,plain,(
    ! [A_122,B_123] :
      ( r2_hidden('#skF_3'(A_122,B_123,A_122),A_122)
      | k4_xboole_0(A_122,B_123) = A_122 ) ),
    inference(resolution,[status(thm)],[c_24,c_469])).

tff(c_28,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_81,plain,(
    ! [D_56,B_57,A_58] :
      ( ~ r2_hidden(D_56,B_57)
      | ~ r2_hidden(D_56,k4_xboole_0(A_58,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_88,plain,(
    ! [D_56,A_13] :
      ( ~ r2_hidden(D_56,k1_xboole_0)
      | ~ r2_hidden(D_56,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_81])).

tff(c_516,plain,(
    ! [B_126,A_127] :
      ( ~ r2_hidden('#skF_3'(k1_xboole_0,B_126,k1_xboole_0),A_127)
      | k4_xboole_0(k1_xboole_0,B_126) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_480,c_88])).

tff(c_535,plain,(
    ! [B_7] : k4_xboole_0(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_478,c_516])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_31629,plain,(
    ! [A_774,B_775,B_776] :
      ( r2_hidden(k4_tarski('#skF_5'(k4_xboole_0(A_774,B_775),B_776),'#skF_4'(k4_xboole_0(A_774,B_775),B_776)),A_774)
      | r2_hidden(k4_tarski('#skF_6'(k4_xboole_0(A_774,B_775),B_776),'#skF_7'(k4_xboole_0(A_774,B_775),B_776)),B_776)
      | k4_relat_1(k4_xboole_0(A_774,B_775)) = B_776
      | ~ v1_relat_1(B_776)
      | ~ v1_relat_1(k4_xboole_0(A_774,B_775)) ) ),
    inference(resolution,[status(thm)],[c_936,c_12])).

tff(c_31741,plain,(
    ! [A_774,B_775,A_13] :
      ( ~ r2_hidden(k4_tarski('#skF_6'(k4_xboole_0(A_774,B_775),k1_xboole_0),'#skF_7'(k4_xboole_0(A_774,B_775),k1_xboole_0)),A_13)
      | r2_hidden(k4_tarski('#skF_5'(k4_xboole_0(A_774,B_775),k1_xboole_0),'#skF_4'(k4_xboole_0(A_774,B_775),k1_xboole_0)),A_774)
      | k4_relat_1(k4_xboole_0(A_774,B_775)) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_xboole_0(A_774,B_775)) ) ),
    inference(resolution,[status(thm)],[c_31629,c_88])).

tff(c_179525,plain,(
    ! [A_2175,B_2176,A_2177] :
      ( ~ r2_hidden(k4_tarski('#skF_6'(k4_xboole_0(A_2175,B_2176),k1_xboole_0),'#skF_7'(k4_xboole_0(A_2175,B_2176),k1_xboole_0)),A_2177)
      | r2_hidden(k4_tarski('#skF_5'(k4_xboole_0(A_2175,B_2176),k1_xboole_0),'#skF_4'(k4_xboole_0(A_2175,B_2176),k1_xboole_0)),A_2175)
      | k4_relat_1(k4_xboole_0(A_2175,B_2176)) = k1_xboole_0
      | ~ v1_relat_1(k4_xboole_0(A_2175,B_2176)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_31741])).

tff(c_179752,plain,(
    ! [B_7,A_2177] :
      ( ~ r2_hidden(k4_tarski('#skF_6'(k1_xboole_0,k1_xboole_0),'#skF_7'(k4_xboole_0(k1_xboole_0,B_7),k1_xboole_0)),A_2177)
      | r2_hidden(k4_tarski('#skF_5'(k4_xboole_0(k1_xboole_0,B_7),k1_xboole_0),'#skF_4'(k4_xboole_0(k1_xboole_0,B_7),k1_xboole_0)),k1_xboole_0)
      | k4_relat_1(k4_xboole_0(k1_xboole_0,B_7)) = k1_xboole_0
      | ~ v1_relat_1(k4_xboole_0(k1_xboole_0,B_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_179525])).

tff(c_179864,plain,(
    ! [A_2177] :
      ( ~ r2_hidden(k4_tarski('#skF_6'(k1_xboole_0,k1_xboole_0),'#skF_7'(k1_xboole_0,k1_xboole_0)),A_2177)
      | r2_hidden(k4_tarski('#skF_5'(k1_xboole_0,k1_xboole_0),'#skF_4'(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | k4_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_535,c_535,c_535,c_535,c_535,c_179752])).

tff(c_179865,plain,(
    ! [A_2177] :
      ( ~ r2_hidden(k4_tarski('#skF_6'(k1_xboole_0,k1_xboole_0),'#skF_7'(k1_xboole_0,k1_xboole_0)),A_2177)
      | r2_hidden(k4_tarski('#skF_5'(k1_xboole_0,k1_xboole_0),'#skF_4'(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_179864])).

tff(c_183109,plain,(
    ! [A_2187] : ~ r2_hidden(k4_tarski('#skF_6'(k1_xboole_0,k1_xboole_0),'#skF_7'(k1_xboole_0,k1_xboole_0)),A_2187) ),
    inference(splitLeft,[status(thm)],[c_179865])).

tff(c_183125,plain,(
    ! [B_2,B_536] :
      ( ~ r1_tarski(k1_xboole_0,B_2)
      | r2_hidden(k4_tarski('#skF_5'(k1_xboole_0,k1_xboole_0),'#skF_4'(k1_xboole_0,k1_xboole_0)),B_536)
      | ~ r1_tarski(k1_xboole_0,B_536)
      | k4_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_13145,c_183109])).

tff(c_183176,plain,(
    ! [B_536] :
      ( r2_hidden(k4_tarski('#skF_5'(k1_xboole_0,k1_xboole_0),'#skF_4'(k1_xboole_0,k1_xboole_0)),B_536)
      | k4_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_26,c_26,c_183125])).

tff(c_183177,plain,(
    ! [B_536] : r2_hidden(k4_tarski('#skF_5'(k1_xboole_0,k1_xboole_0),'#skF_4'(k1_xboole_0,k1_xboole_0)),B_536) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_183176])).

tff(c_183205,plain,(
    ! [B_2188] : r2_hidden(k4_tarski('#skF_5'(k1_xboole_0,k1_xboole_0),'#skF_4'(k1_xboole_0,k1_xboole_0)),B_2188) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_183176])).

tff(c_18,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),B_7)
      | ~ r2_hidden('#skF_3'(A_6,B_7,C_8),A_6)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_748,plain,(
    ! [A_145,B_146,C_147] :
      ( ~ r2_hidden('#skF_2'(A_145,B_146,C_147),C_147)
      | r2_hidden('#skF_3'(A_145,B_146,C_147),B_146)
      | ~ r2_hidden('#skF_3'(A_145,B_146,C_147),A_145)
      | k4_xboole_0(A_145,B_146) = C_147 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1409,plain,(
    ! [A_224,B_225] :
      ( r2_hidden('#skF_3'(A_224,B_225,A_224),B_225)
      | ~ r2_hidden('#skF_3'(A_224,B_225,A_224),A_224)
      | k4_xboole_0(A_224,B_225) = A_224 ) ),
    inference(resolution,[status(thm)],[c_18,c_748])).

tff(c_1436,plain,(
    ! [A_226,B_227] :
      ( r2_hidden('#skF_3'(A_226,B_227,A_226),B_227)
      | k4_xboole_0(A_226,B_227) = A_226 ) ),
    inference(resolution,[status(thm)],[c_478,c_1409])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1667,plain,(
    ! [A_250,A_251,B_252] :
      ( ~ r2_hidden('#skF_3'(A_250,k4_xboole_0(A_251,B_252),A_250),B_252)
      | k4_xboole_0(A_250,k4_xboole_0(A_251,B_252)) = A_250 ) ),
    inference(resolution,[status(thm)],[c_1436,c_10])).

tff(c_1714,plain,(
    ! [A_6,A_251] : k4_xboole_0(A_6,k4_xboole_0(A_251,A_6)) = A_6 ),
    inference(resolution,[status(thm)],[c_478,c_1667])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_96,plain,(
    ! [D_61,A_62,B_63] :
      ( r2_hidden(D_61,A_62)
      | ~ r2_hidden(D_61,k4_xboole_0(A_62,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_242,plain,(
    ! [A_92,B_93,B_94] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_92,B_93),B_94),A_92)
      | r1_tarski(k4_xboole_0(A_92,B_93),B_94) ) ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_271,plain,(
    ! [A_92,B_93] : r1_tarski(k4_xboole_0(A_92,B_93),A_92) ),
    inference(resolution,[status(thm)],[c_242,c_4])).

tff(c_502,plain,(
    ! [A_122,B_123,B_2] :
      ( r2_hidden('#skF_3'(A_122,B_123,A_122),B_2)
      | ~ r1_tarski(A_122,B_2)
      | k4_xboole_0(A_122,B_123) = A_122 ) ),
    inference(resolution,[status(thm)],[c_480,c_2])).

tff(c_2108,plain,(
    ! [A_263,B_264,A_265] :
      ( ~ r1_tarski(A_263,B_264)
      | k4_xboole_0(A_263,k4_xboole_0(A_265,B_264)) = A_263 ) ),
    inference(resolution,[status(thm)],[c_502,c_1667])).

tff(c_2749,plain,(
    ! [A_295,B_296,A_297] :
      ( k4_xboole_0(k4_xboole_0(A_295,B_296),A_297) = k4_xboole_0(A_295,B_296)
      | ~ r1_tarski(A_297,B_296) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2108,c_1714])).

tff(c_2900,plain,(
    ! [A_6,A_251,A_297] :
      ( k4_xboole_0(A_6,k4_xboole_0(A_251,A_6)) = k4_xboole_0(A_6,A_297)
      | ~ r1_tarski(A_297,k4_xboole_0(A_251,A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1714,c_2749])).

tff(c_2948,plain,(
    ! [A_298,A_299,A_300] :
      ( k4_xboole_0(A_298,A_299) = A_298
      | ~ r1_tarski(A_299,k4_xboole_0(A_300,A_298)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1714,c_2900])).

tff(c_3044,plain,(
    ! [A_304,A_305,B_306] : k4_xboole_0(A_304,k4_xboole_0(k4_xboole_0(A_305,A_304),B_306)) = A_304 ),
    inference(resolution,[status(thm)],[c_271,c_2948])).

tff(c_3560,plain,(
    ! [A_318,A_319,B_320] : k4_xboole_0(k4_xboole_0(A_318,A_319),k4_xboole_0(A_319,B_320)) = k4_xboole_0(A_318,A_319) ),
    inference(superposition,[status(thm),theory(equality)],[c_1714,c_3044])).

tff(c_3641,plain,(
    ! [A_319,B_320,A_318] : k4_xboole_0(k4_xboole_0(A_319,B_320),k4_xboole_0(A_318,A_319)) = k4_xboole_0(A_319,B_320) ),
    inference(superposition,[status(thm),theory(equality)],[c_3560,c_1714])).

tff(c_4058,plain,(
    ! [A_329,B_330,A_331] : k4_xboole_0(k4_xboole_0(A_329,B_330),k4_xboole_0(A_331,A_329)) = k4_xboole_0(A_329,B_330) ),
    inference(superposition,[status(thm),theory(equality)],[c_3560,c_1714])).

tff(c_1720,plain,(
    ! [A_253,A_254] : k4_xboole_0(A_253,k4_xboole_0(A_254,A_253)) = A_253 ),
    inference(resolution,[status(thm)],[c_478,c_1667])).

tff(c_1798,plain,(
    ! [D_11,A_254,A_253] :
      ( ~ r2_hidden(D_11,k4_xboole_0(A_254,A_253))
      | ~ r2_hidden(D_11,A_253) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1720,c_10])).

tff(c_4818,plain,(
    ! [D_339,A_340,B_341,A_342] :
      ( ~ r2_hidden(D_339,k4_xboole_0(A_340,B_341))
      | ~ r2_hidden(D_339,k4_xboole_0(A_342,A_340)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4058,c_1798])).

tff(c_4825,plain,(
    ! [D_339,A_319,B_320,A_342] :
      ( ~ r2_hidden(D_339,k4_xboole_0(A_319,B_320))
      | ~ r2_hidden(D_339,k4_xboole_0(A_342,k4_xboole_0(A_319,B_320))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3641,c_4818])).

tff(c_183226,plain,(
    ! [A_319,B_320] : ~ r2_hidden(k4_tarski('#skF_5'(k1_xboole_0,k1_xboole_0),'#skF_4'(k1_xboole_0,k1_xboole_0)),k4_xboole_0(A_319,B_320)) ),
    inference(resolution,[status(thm)],[c_183205,c_4825])).

tff(c_183327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_183177,c_183226])).

tff(c_183328,plain,(
    r2_hidden(k4_tarski('#skF_5'(k1_xboole_0,k1_xboole_0),'#skF_4'(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_179865])).

tff(c_293,plain,(
    ! [A_99,B_100,C_101] :
      ( ~ r2_hidden('#skF_2'(A_99,B_100,C_101),B_100)
      | r2_hidden('#skF_3'(A_99,B_100,C_101),C_101)
      | k4_xboole_0(A_99,B_100) = C_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_300,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,A_6,C_8),C_8)
      | k4_xboole_0(A_6,A_6) = C_8 ) ),
    inference(resolution,[status(thm)],[c_24,c_293])).

tff(c_302,plain,(
    ! [A_102,C_103] :
      ( r2_hidden('#skF_3'(A_102,A_102,C_103),C_103)
      | k4_xboole_0(A_102,A_102) = C_103 ) ),
    inference(resolution,[status(thm)],[c_24,c_293])).

tff(c_334,plain,(
    ! [A_106,A_107] :
      ( ~ r2_hidden('#skF_3'(A_106,A_106,k1_xboole_0),A_107)
      | k4_xboole_0(A_106,A_106) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_302,c_88])).

tff(c_350,plain,(
    ! [A_108] : k4_xboole_0(A_108,A_108) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_300,c_334])).

tff(c_367,plain,(
    ! [D_11,A_108] :
      ( r2_hidden(D_11,A_108)
      | ~ r2_hidden(D_11,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_12])).

tff(c_183366,plain,(
    ! [A_108] : r2_hidden(k4_tarski('#skF_5'(k1_xboole_0,k1_xboole_0),'#skF_4'(k1_xboole_0,k1_xboole_0)),A_108) ),
    inference(resolution,[status(thm)],[c_183328,c_367])).

tff(c_183373,plain,(
    ! [A_2189] : r2_hidden(k4_tarski('#skF_5'(k1_xboole_0,k1_xboole_0),'#skF_4'(k1_xboole_0,k1_xboole_0)),A_2189) ),
    inference(resolution,[status(thm)],[c_183328,c_367])).

tff(c_183394,plain,(
    ! [A_319,B_320] : ~ r2_hidden(k4_tarski('#skF_5'(k1_xboole_0,k1_xboole_0),'#skF_4'(k1_xboole_0,k1_xboole_0)),k4_xboole_0(A_319,B_320)) ),
    inference(resolution,[status(thm)],[c_183373,c_4825])).

tff(c_183495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_183366,c_183394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:00:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 54.26/42.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 54.26/42.73  
% 54.26/42.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 54.26/42.73  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k4_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 54.26/42.73  
% 54.26/42.73  %Foreground sorts:
% 54.26/42.73  
% 54.26/42.73  
% 54.26/42.73  %Background operators:
% 54.26/42.73  
% 54.26/42.73  
% 54.26/42.73  %Foreground operators:
% 54.26/42.73  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 54.26/42.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 54.26/42.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 54.26/42.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 54.26/42.73  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 54.26/42.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 54.26/42.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 54.26/42.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 54.26/42.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 54.26/42.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 54.26/42.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 54.26/42.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 54.26/42.73  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 54.26/42.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 54.26/42.73  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 54.26/42.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 54.26/42.73  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 54.26/42.73  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 54.26/42.73  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 54.26/42.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 54.26/42.73  
% 54.26/42.75  tff(f_77, negated_conjecture, ~(k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_relat_1)).
% 54.26/42.75  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 54.26/42.75  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 54.26/42.75  tff(f_75, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_relat_1)).
% 54.26/42.75  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 54.26/42.75  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((B = k4_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> r2_hidden(k4_tarski(D, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_relat_1)).
% 54.26/42.75  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 54.26/42.75  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 54.26/42.75  tff(f_46, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 54.26/42.75  tff(c_50, plain, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 54.26/42.75  tff(c_30, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 54.26/42.75  tff(c_62, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_61])).
% 54.26/42.75  tff(c_66, plain, (![A_14]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_14))), inference(resolution, [status(thm)], [c_30, c_62])).
% 54.26/42.75  tff(c_68, plain, (![A_14]: (~v1_relat_1(A_14))), inference(splitLeft, [status(thm)], [c_66])).
% 54.26/42.75  tff(c_48, plain, (![A_38, B_39, C_40, D_41]: (v1_relat_1(k2_tarski(k4_tarski(A_38, B_39), k4_tarski(C_40, D_41))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 54.26/42.75  tff(c_71, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_48])).
% 54.26/42.75  tff(c_72, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_66])).
% 54.26/42.75  tff(c_26, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 54.26/42.75  tff(c_936, plain, (![A_163, B_164]: (r2_hidden(k4_tarski('#skF_5'(A_163, B_164), '#skF_4'(A_163, B_164)), A_163) | r2_hidden(k4_tarski('#skF_6'(A_163, B_164), '#skF_7'(A_163, B_164)), B_164) | k4_relat_1(A_163)=B_164 | ~v1_relat_1(B_164) | ~v1_relat_1(A_163))), inference(cnfTransformation, [status(thm)], [f_73])).
% 54.26/42.75  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 54.26/42.75  tff(c_13032, plain, (![A_534, B_535, B_536]: (r2_hidden(k4_tarski('#skF_5'(A_534, B_535), '#skF_4'(A_534, B_535)), B_536) | ~r1_tarski(A_534, B_536) | r2_hidden(k4_tarski('#skF_6'(A_534, B_535), '#skF_7'(A_534, B_535)), B_535) | k4_relat_1(A_534)=B_535 | ~v1_relat_1(B_535) | ~v1_relat_1(A_534))), inference(resolution, [status(thm)], [c_936, c_2])).
% 54.26/42.75  tff(c_13145, plain, (![A_534, B_535, B_2, B_536]: (r2_hidden(k4_tarski('#skF_6'(A_534, B_535), '#skF_7'(A_534, B_535)), B_2) | ~r1_tarski(B_535, B_2) | r2_hidden(k4_tarski('#skF_5'(A_534, B_535), '#skF_4'(A_534, B_535)), B_536) | ~r1_tarski(A_534, B_536) | k4_relat_1(A_534)=B_535 | ~v1_relat_1(B_535) | ~v1_relat_1(A_534))), inference(resolution, [status(thm)], [c_13032, c_2])).
% 54.26/42.75  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 54.26/42.75  tff(c_469, plain, (![A_119, B_120, C_121]: (~r2_hidden('#skF_2'(A_119, B_120, C_121), C_121) | r2_hidden('#skF_3'(A_119, B_120, C_121), C_121) | k4_xboole_0(A_119, B_120)=C_121)), inference(cnfTransformation, [status(thm)], [f_42])).
% 54.26/42.75  tff(c_478, plain, (![A_6, B_7]: (r2_hidden('#skF_3'(A_6, B_7, A_6), A_6) | k4_xboole_0(A_6, B_7)=A_6)), inference(resolution, [status(thm)], [c_24, c_469])).
% 54.26/42.75  tff(c_480, plain, (![A_122, B_123]: (r2_hidden('#skF_3'(A_122, B_123, A_122), A_122) | k4_xboole_0(A_122, B_123)=A_122)), inference(resolution, [status(thm)], [c_24, c_469])).
% 54.26/42.75  tff(c_28, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_46])).
% 54.26/42.75  tff(c_81, plain, (![D_56, B_57, A_58]: (~r2_hidden(D_56, B_57) | ~r2_hidden(D_56, k4_xboole_0(A_58, B_57)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 54.26/42.75  tff(c_88, plain, (![D_56, A_13]: (~r2_hidden(D_56, k1_xboole_0) | ~r2_hidden(D_56, A_13))), inference(superposition, [status(thm), theory('equality')], [c_28, c_81])).
% 54.26/42.75  tff(c_516, plain, (![B_126, A_127]: (~r2_hidden('#skF_3'(k1_xboole_0, B_126, k1_xboole_0), A_127) | k4_xboole_0(k1_xboole_0, B_126)=k1_xboole_0)), inference(resolution, [status(thm)], [c_480, c_88])).
% 54.26/42.75  tff(c_535, plain, (![B_7]: (k4_xboole_0(k1_xboole_0, B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_478, c_516])).
% 54.26/42.75  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 54.26/42.75  tff(c_31629, plain, (![A_774, B_775, B_776]: (r2_hidden(k4_tarski('#skF_5'(k4_xboole_0(A_774, B_775), B_776), '#skF_4'(k4_xboole_0(A_774, B_775), B_776)), A_774) | r2_hidden(k4_tarski('#skF_6'(k4_xboole_0(A_774, B_775), B_776), '#skF_7'(k4_xboole_0(A_774, B_775), B_776)), B_776) | k4_relat_1(k4_xboole_0(A_774, B_775))=B_776 | ~v1_relat_1(B_776) | ~v1_relat_1(k4_xboole_0(A_774, B_775)))), inference(resolution, [status(thm)], [c_936, c_12])).
% 54.26/42.75  tff(c_31741, plain, (![A_774, B_775, A_13]: (~r2_hidden(k4_tarski('#skF_6'(k4_xboole_0(A_774, B_775), k1_xboole_0), '#skF_7'(k4_xboole_0(A_774, B_775), k1_xboole_0)), A_13) | r2_hidden(k4_tarski('#skF_5'(k4_xboole_0(A_774, B_775), k1_xboole_0), '#skF_4'(k4_xboole_0(A_774, B_775), k1_xboole_0)), A_774) | k4_relat_1(k4_xboole_0(A_774, B_775))=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_xboole_0(A_774, B_775)))), inference(resolution, [status(thm)], [c_31629, c_88])).
% 54.26/42.75  tff(c_179525, plain, (![A_2175, B_2176, A_2177]: (~r2_hidden(k4_tarski('#skF_6'(k4_xboole_0(A_2175, B_2176), k1_xboole_0), '#skF_7'(k4_xboole_0(A_2175, B_2176), k1_xboole_0)), A_2177) | r2_hidden(k4_tarski('#skF_5'(k4_xboole_0(A_2175, B_2176), k1_xboole_0), '#skF_4'(k4_xboole_0(A_2175, B_2176), k1_xboole_0)), A_2175) | k4_relat_1(k4_xboole_0(A_2175, B_2176))=k1_xboole_0 | ~v1_relat_1(k4_xboole_0(A_2175, B_2176)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_31741])).
% 54.26/42.75  tff(c_179752, plain, (![B_7, A_2177]: (~r2_hidden(k4_tarski('#skF_6'(k1_xboole_0, k1_xboole_0), '#skF_7'(k4_xboole_0(k1_xboole_0, B_7), k1_xboole_0)), A_2177) | r2_hidden(k4_tarski('#skF_5'(k4_xboole_0(k1_xboole_0, B_7), k1_xboole_0), '#skF_4'(k4_xboole_0(k1_xboole_0, B_7), k1_xboole_0)), k1_xboole_0) | k4_relat_1(k4_xboole_0(k1_xboole_0, B_7))=k1_xboole_0 | ~v1_relat_1(k4_xboole_0(k1_xboole_0, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_535, c_179525])).
% 54.26/42.75  tff(c_179864, plain, (![A_2177]: (~r2_hidden(k4_tarski('#skF_6'(k1_xboole_0, k1_xboole_0), '#skF_7'(k1_xboole_0, k1_xboole_0)), A_2177) | r2_hidden(k4_tarski('#skF_5'(k1_xboole_0, k1_xboole_0), '#skF_4'(k1_xboole_0, k1_xboole_0)), k1_xboole_0) | k4_relat_1(k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_535, c_535, c_535, c_535, c_535, c_179752])).
% 54.26/42.75  tff(c_179865, plain, (![A_2177]: (~r2_hidden(k4_tarski('#skF_6'(k1_xboole_0, k1_xboole_0), '#skF_7'(k1_xboole_0, k1_xboole_0)), A_2177) | r2_hidden(k4_tarski('#skF_5'(k1_xboole_0, k1_xboole_0), '#skF_4'(k1_xboole_0, k1_xboole_0)), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_50, c_179864])).
% 54.26/42.75  tff(c_183109, plain, (![A_2187]: (~r2_hidden(k4_tarski('#skF_6'(k1_xboole_0, k1_xboole_0), '#skF_7'(k1_xboole_0, k1_xboole_0)), A_2187))), inference(splitLeft, [status(thm)], [c_179865])).
% 54.26/42.75  tff(c_183125, plain, (![B_2, B_536]: (~r1_tarski(k1_xboole_0, B_2) | r2_hidden(k4_tarski('#skF_5'(k1_xboole_0, k1_xboole_0), '#skF_4'(k1_xboole_0, k1_xboole_0)), B_536) | ~r1_tarski(k1_xboole_0, B_536) | k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_13145, c_183109])).
% 54.26/42.75  tff(c_183176, plain, (![B_536]: (r2_hidden(k4_tarski('#skF_5'(k1_xboole_0, k1_xboole_0), '#skF_4'(k1_xboole_0, k1_xboole_0)), B_536) | k4_relat_1(k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_26, c_26, c_183125])).
% 54.26/42.75  tff(c_183177, plain, (![B_536]: (r2_hidden(k4_tarski('#skF_5'(k1_xboole_0, k1_xboole_0), '#skF_4'(k1_xboole_0, k1_xboole_0)), B_536))), inference(negUnitSimplification, [status(thm)], [c_50, c_183176])).
% 54.26/42.75  tff(c_183205, plain, (![B_2188]: (r2_hidden(k4_tarski('#skF_5'(k1_xboole_0, k1_xboole_0), '#skF_4'(k1_xboole_0, k1_xboole_0)), B_2188))), inference(negUnitSimplification, [status(thm)], [c_50, c_183176])).
% 54.26/42.75  tff(c_18, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), B_7) | ~r2_hidden('#skF_3'(A_6, B_7, C_8), A_6) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 54.26/42.75  tff(c_748, plain, (![A_145, B_146, C_147]: (~r2_hidden('#skF_2'(A_145, B_146, C_147), C_147) | r2_hidden('#skF_3'(A_145, B_146, C_147), B_146) | ~r2_hidden('#skF_3'(A_145, B_146, C_147), A_145) | k4_xboole_0(A_145, B_146)=C_147)), inference(cnfTransformation, [status(thm)], [f_42])).
% 54.26/42.75  tff(c_1409, plain, (![A_224, B_225]: (r2_hidden('#skF_3'(A_224, B_225, A_224), B_225) | ~r2_hidden('#skF_3'(A_224, B_225, A_224), A_224) | k4_xboole_0(A_224, B_225)=A_224)), inference(resolution, [status(thm)], [c_18, c_748])).
% 54.26/42.75  tff(c_1436, plain, (![A_226, B_227]: (r2_hidden('#skF_3'(A_226, B_227, A_226), B_227) | k4_xboole_0(A_226, B_227)=A_226)), inference(resolution, [status(thm)], [c_478, c_1409])).
% 54.26/42.75  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 54.26/42.75  tff(c_1667, plain, (![A_250, A_251, B_252]: (~r2_hidden('#skF_3'(A_250, k4_xboole_0(A_251, B_252), A_250), B_252) | k4_xboole_0(A_250, k4_xboole_0(A_251, B_252))=A_250)), inference(resolution, [status(thm)], [c_1436, c_10])).
% 54.26/42.75  tff(c_1714, plain, (![A_6, A_251]: (k4_xboole_0(A_6, k4_xboole_0(A_251, A_6))=A_6)), inference(resolution, [status(thm)], [c_478, c_1667])).
% 54.26/42.75  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 54.26/42.75  tff(c_96, plain, (![D_61, A_62, B_63]: (r2_hidden(D_61, A_62) | ~r2_hidden(D_61, k4_xboole_0(A_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 54.26/42.75  tff(c_242, plain, (![A_92, B_93, B_94]: (r2_hidden('#skF_1'(k4_xboole_0(A_92, B_93), B_94), A_92) | r1_tarski(k4_xboole_0(A_92, B_93), B_94))), inference(resolution, [status(thm)], [c_6, c_96])).
% 54.26/42.75  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 54.26/42.75  tff(c_271, plain, (![A_92, B_93]: (r1_tarski(k4_xboole_0(A_92, B_93), A_92))), inference(resolution, [status(thm)], [c_242, c_4])).
% 54.26/42.75  tff(c_502, plain, (![A_122, B_123, B_2]: (r2_hidden('#skF_3'(A_122, B_123, A_122), B_2) | ~r1_tarski(A_122, B_2) | k4_xboole_0(A_122, B_123)=A_122)), inference(resolution, [status(thm)], [c_480, c_2])).
% 54.26/42.75  tff(c_2108, plain, (![A_263, B_264, A_265]: (~r1_tarski(A_263, B_264) | k4_xboole_0(A_263, k4_xboole_0(A_265, B_264))=A_263)), inference(resolution, [status(thm)], [c_502, c_1667])).
% 54.26/42.75  tff(c_2749, plain, (![A_295, B_296, A_297]: (k4_xboole_0(k4_xboole_0(A_295, B_296), A_297)=k4_xboole_0(A_295, B_296) | ~r1_tarski(A_297, B_296))), inference(superposition, [status(thm), theory('equality')], [c_2108, c_1714])).
% 54.26/42.75  tff(c_2900, plain, (![A_6, A_251, A_297]: (k4_xboole_0(A_6, k4_xboole_0(A_251, A_6))=k4_xboole_0(A_6, A_297) | ~r1_tarski(A_297, k4_xboole_0(A_251, A_6)))), inference(superposition, [status(thm), theory('equality')], [c_1714, c_2749])).
% 54.26/42.75  tff(c_2948, plain, (![A_298, A_299, A_300]: (k4_xboole_0(A_298, A_299)=A_298 | ~r1_tarski(A_299, k4_xboole_0(A_300, A_298)))), inference(demodulation, [status(thm), theory('equality')], [c_1714, c_2900])).
% 54.26/42.75  tff(c_3044, plain, (![A_304, A_305, B_306]: (k4_xboole_0(A_304, k4_xboole_0(k4_xboole_0(A_305, A_304), B_306))=A_304)), inference(resolution, [status(thm)], [c_271, c_2948])).
% 54.26/42.75  tff(c_3560, plain, (![A_318, A_319, B_320]: (k4_xboole_0(k4_xboole_0(A_318, A_319), k4_xboole_0(A_319, B_320))=k4_xboole_0(A_318, A_319))), inference(superposition, [status(thm), theory('equality')], [c_1714, c_3044])).
% 54.26/42.75  tff(c_3641, plain, (![A_319, B_320, A_318]: (k4_xboole_0(k4_xboole_0(A_319, B_320), k4_xboole_0(A_318, A_319))=k4_xboole_0(A_319, B_320))), inference(superposition, [status(thm), theory('equality')], [c_3560, c_1714])).
% 54.26/42.75  tff(c_4058, plain, (![A_329, B_330, A_331]: (k4_xboole_0(k4_xboole_0(A_329, B_330), k4_xboole_0(A_331, A_329))=k4_xboole_0(A_329, B_330))), inference(superposition, [status(thm), theory('equality')], [c_3560, c_1714])).
% 54.26/42.75  tff(c_1720, plain, (![A_253, A_254]: (k4_xboole_0(A_253, k4_xboole_0(A_254, A_253))=A_253)), inference(resolution, [status(thm)], [c_478, c_1667])).
% 54.26/42.75  tff(c_1798, plain, (![D_11, A_254, A_253]: (~r2_hidden(D_11, k4_xboole_0(A_254, A_253)) | ~r2_hidden(D_11, A_253))), inference(superposition, [status(thm), theory('equality')], [c_1720, c_10])).
% 54.26/42.75  tff(c_4818, plain, (![D_339, A_340, B_341, A_342]: (~r2_hidden(D_339, k4_xboole_0(A_340, B_341)) | ~r2_hidden(D_339, k4_xboole_0(A_342, A_340)))), inference(superposition, [status(thm), theory('equality')], [c_4058, c_1798])).
% 54.26/42.75  tff(c_4825, plain, (![D_339, A_319, B_320, A_342]: (~r2_hidden(D_339, k4_xboole_0(A_319, B_320)) | ~r2_hidden(D_339, k4_xboole_0(A_342, k4_xboole_0(A_319, B_320))))), inference(superposition, [status(thm), theory('equality')], [c_3641, c_4818])).
% 54.26/42.75  tff(c_183226, plain, (![A_319, B_320]: (~r2_hidden(k4_tarski('#skF_5'(k1_xboole_0, k1_xboole_0), '#skF_4'(k1_xboole_0, k1_xboole_0)), k4_xboole_0(A_319, B_320)))), inference(resolution, [status(thm)], [c_183205, c_4825])).
% 54.26/42.75  tff(c_183327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_183177, c_183226])).
% 54.26/42.75  tff(c_183328, plain, (r2_hidden(k4_tarski('#skF_5'(k1_xboole_0, k1_xboole_0), '#skF_4'(k1_xboole_0, k1_xboole_0)), k1_xboole_0)), inference(splitRight, [status(thm)], [c_179865])).
% 54.26/42.75  tff(c_293, plain, (![A_99, B_100, C_101]: (~r2_hidden('#skF_2'(A_99, B_100, C_101), B_100) | r2_hidden('#skF_3'(A_99, B_100, C_101), C_101) | k4_xboole_0(A_99, B_100)=C_101)), inference(cnfTransformation, [status(thm)], [f_42])).
% 54.26/42.75  tff(c_300, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, A_6, C_8), C_8) | k4_xboole_0(A_6, A_6)=C_8)), inference(resolution, [status(thm)], [c_24, c_293])).
% 54.26/42.75  tff(c_302, plain, (![A_102, C_103]: (r2_hidden('#skF_3'(A_102, A_102, C_103), C_103) | k4_xboole_0(A_102, A_102)=C_103)), inference(resolution, [status(thm)], [c_24, c_293])).
% 54.26/42.75  tff(c_334, plain, (![A_106, A_107]: (~r2_hidden('#skF_3'(A_106, A_106, k1_xboole_0), A_107) | k4_xboole_0(A_106, A_106)=k1_xboole_0)), inference(resolution, [status(thm)], [c_302, c_88])).
% 54.26/42.75  tff(c_350, plain, (![A_108]: (k4_xboole_0(A_108, A_108)=k1_xboole_0)), inference(resolution, [status(thm)], [c_300, c_334])).
% 54.26/42.75  tff(c_367, plain, (![D_11, A_108]: (r2_hidden(D_11, A_108) | ~r2_hidden(D_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_350, c_12])).
% 54.26/42.75  tff(c_183366, plain, (![A_108]: (r2_hidden(k4_tarski('#skF_5'(k1_xboole_0, k1_xboole_0), '#skF_4'(k1_xboole_0, k1_xboole_0)), A_108))), inference(resolution, [status(thm)], [c_183328, c_367])).
% 54.26/42.75  tff(c_183373, plain, (![A_2189]: (r2_hidden(k4_tarski('#skF_5'(k1_xboole_0, k1_xboole_0), '#skF_4'(k1_xboole_0, k1_xboole_0)), A_2189))), inference(resolution, [status(thm)], [c_183328, c_367])).
% 54.26/42.75  tff(c_183394, plain, (![A_319, B_320]: (~r2_hidden(k4_tarski('#skF_5'(k1_xboole_0, k1_xboole_0), '#skF_4'(k1_xboole_0, k1_xboole_0)), k4_xboole_0(A_319, B_320)))), inference(resolution, [status(thm)], [c_183373, c_4825])).
% 54.26/42.75  tff(c_183495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_183366, c_183394])).
% 54.26/42.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 54.26/42.75  
% 54.26/42.75  Inference rules
% 54.26/42.75  ----------------------
% 54.26/42.75  #Ref     : 0
% 54.26/42.75  #Sup     : 50910
% 54.26/42.75  #Fact    : 0
% 54.26/42.75  #Define  : 0
% 54.26/42.75  #Split   : 10
% 54.26/42.75  #Chain   : 0
% 54.26/42.75  #Close   : 0
% 54.26/42.75  
% 54.26/42.75  Ordering : KBO
% 54.26/42.75  
% 54.26/42.75  Simplification rules
% 54.26/42.75  ----------------------
% 54.26/42.75  #Subsume      : 22013
% 54.26/42.75  #Demod        : 27963
% 54.26/42.75  #Tautology    : 9558
% 54.26/42.75  #SimpNegUnit  : 90
% 54.26/42.75  #BackRed      : 24
% 54.26/42.75  
% 54.26/42.75  #Partial instantiations: 0
% 54.26/42.75  #Strategies tried      : 1
% 54.26/42.75  
% 54.26/42.75  Timing (in seconds)
% 54.26/42.75  ----------------------
% 54.26/42.75  Preprocessing        : 0.38
% 54.26/42.75  Parsing              : 0.21
% 54.26/42.75  CNF conversion       : 0.03
% 54.26/42.75  Main loop            : 41.58
% 54.26/42.75  Inferencing          : 3.68
% 54.26/42.75  Reduction            : 9.40
% 54.26/42.75  Demodulation         : 7.85
% 54.26/42.75  BG Simplification    : 0.48
% 54.26/42.75  Subsumption          : 26.32
% 54.26/42.75  Abstraction          : 0.79
% 54.26/42.75  MUC search           : 0.00
% 54.26/42.75  Cooper               : 0.00
% 54.26/42.75  Total                : 42.00
% 54.26/42.75  Index Insertion      : 0.00
% 54.26/42.75  Index Deletion       : 0.00
% 54.26/42.75  Index Matching       : 0.00
% 54.26/42.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
