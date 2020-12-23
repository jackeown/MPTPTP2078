%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0281+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:02 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 128 expanded)
%              Number of leaves         :   19 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :   90 ( 254 expanded)
%              Number of equality atoms :   12 (  50 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_52,axiom,(
    ! [A,B] :
      ( r3_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        | r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)) = k1_zfmisc_1(k2_xboole_0(A,B))
       => r3_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_54,plain,(
    ! [A_19,B_20] :
      ( ~ r1_tarski(A_19,B_20)
      | r3_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_44,plain,(
    ~ r3_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_58,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_44])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ! [C_7,A_3] :
      ( r2_hidden(C_7,k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    k2_xboole_0(k1_zfmisc_1('#skF_5'),k1_zfmisc_1('#skF_6')) = k1_zfmisc_1(k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_104,plain,(
    ! [D_37,B_38,A_39] :
      ( r2_hidden(D_37,B_38)
      | r2_hidden(D_37,A_39)
      | ~ r2_hidden(D_37,k2_xboole_0(A_39,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_131,plain,(
    ! [D_43] :
      ( r2_hidden(D_43,k1_zfmisc_1('#skF_6'))
      | r2_hidden(D_43,k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(D_43,k1_zfmisc_1(k2_xboole_0('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_104])).

tff(c_274,plain,(
    ! [C_55] :
      ( r2_hidden(C_55,k1_zfmisc_1('#skF_6'))
      | r2_hidden(C_55,k1_zfmisc_1('#skF_5'))
      | ~ r1_tarski(C_55,k2_xboole_0('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_10,c_131])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_287,plain,(
    ! [C_56] :
      ( r1_tarski(C_56,'#skF_5')
      | r2_hidden(C_56,k1_zfmisc_1('#skF_6'))
      | ~ r1_tarski(C_56,k2_xboole_0('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_274,c_8])).

tff(c_311,plain,(
    ! [C_58] :
      ( r1_tarski(C_58,'#skF_6')
      | r1_tarski(C_58,'#skF_5')
      | ~ r1_tarski(C_58,k2_xboole_0('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_287,c_8])).

tff(c_329,plain,
    ( r1_tarski(k2_xboole_0('#skF_5','#skF_6'),'#skF_6')
    | r1_tarski(k2_xboole_0('#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_311])).

tff(c_330,plain,(
    r1_tarski(k2_xboole_0('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_329])).

tff(c_80,plain,(
    ! [D_30,A_31,B_32] :
      ( ~ r2_hidden(D_30,A_31)
      | r2_hidden(D_30,k2_xboole_0(A_31,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_120,plain,(
    ! [D_41] :
      ( ~ r2_hidden(D_41,k1_zfmisc_1('#skF_5'))
      | r2_hidden(D_41,k1_zfmisc_1(k2_xboole_0('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_80])).

tff(c_125,plain,(
    ! [D_42] :
      ( r1_tarski(D_42,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(D_42,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_120,c_8])).

tff(c_145,plain,(
    ! [C_44] :
      ( r1_tarski(C_44,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r1_tarski(C_44,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10,c_125])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_148,plain,(
    ! [C_44] :
      ( k2_xboole_0('#skF_5','#skF_6') = C_44
      | ~ r1_tarski(k2_xboole_0('#skF_5','#skF_6'),C_44)
      | ~ r1_tarski(C_44,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_145,c_2])).

tff(c_333,plain,
    ( k2_xboole_0('#skF_5','#skF_6') = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_330,c_148])).

tff(c_341,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_333])).

tff(c_22,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | r2_hidden(D_13,k2_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_93,plain,(
    ! [D_35] :
      ( ~ r2_hidden(D_35,k1_zfmisc_1('#skF_6'))
      | r2_hidden(D_35,k1_zfmisc_1(k2_xboole_0('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_22])).

tff(c_98,plain,(
    ! [D_36] :
      ( r1_tarski(D_36,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(D_36,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_93,c_8])).

tff(c_103,plain,(
    ! [C_7] :
      ( r1_tarski(C_7,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r1_tarski(C_7,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_10,c_98])).

tff(c_373,plain,(
    ! [C_59] :
      ( r1_tarski(C_59,'#skF_5')
      | ~ r1_tarski(C_59,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_103])).

tff(c_49,plain,(
    ! [B_17,A_18] :
      ( ~ r1_tarski(B_17,A_18)
      | r3_xboole_0(A_18,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_53,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_49,c_44])).

tff(c_382,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_373,c_53])).

tff(c_388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_382])).

tff(c_389,plain,(
    r1_tarski(k2_xboole_0('#skF_5','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_329])).

tff(c_116,plain,(
    ! [C_40] :
      ( r1_tarski(C_40,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r1_tarski(C_40,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_10,c_98])).

tff(c_119,plain,(
    ! [C_40] :
      ( k2_xboole_0('#skF_5','#skF_6') = C_40
      | ~ r1_tarski(k2_xboole_0('#skF_5','#skF_6'),C_40)
      | ~ r1_tarski(C_40,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_116,c_2])).

tff(c_422,plain,
    ( k2_xboole_0('#skF_5','#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_389,c_119])).

tff(c_428,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_422])).

tff(c_130,plain,(
    ! [C_7] :
      ( r1_tarski(C_7,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r1_tarski(C_7,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10,c_125])).

tff(c_473,plain,(
    ! [C_63] :
      ( r1_tarski(C_63,'#skF_6')
      | ~ r1_tarski(C_63,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_130])).

tff(c_479,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_473])).

tff(c_483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_479])).

%------------------------------------------------------------------------------
