%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:17 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 372 expanded)
%              Number of leaves         :   32 ( 141 expanded)
%              Depth                    :   18
%              Number of atoms          :  146 ( 725 expanded)
%              Number of equality atoms :   45 ( 235 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_92,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_38,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_79,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_88,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_1'(A_44),A_44)
      | v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_80,plain,(
    ! [A_41,B_42] : ~ r2_hidden(A_41,k2_zfmisc_1(A_41,B_42)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86,plain,(
    ! [A_3] : ~ r2_hidden(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_80])).

tff(c_93,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_88,c_86])).

tff(c_24,plain,(
    ! [A_26,B_27] :
      ( v1_relat_1(k5_relat_1(A_26,B_27))
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_171,plain,(
    ! [A_63,B_64] :
      ( k1_relat_1(k5_relat_1(A_63,B_64)) = k1_relat_1(A_63)
      | ~ r1_tarski(k2_relat_1(A_63),k1_relat_1(B_64))
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_177,plain,(
    ! [B_64] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_64)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_64))
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_171])).

tff(c_182,plain,(
    ! [B_65] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_65)) = k1_xboole_0
      | ~ v1_relat_1(B_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_6,c_36,c_177])).

tff(c_26,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0(k1_relat_1(A_28))
      | ~ v1_relat_1(A_28)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_191,plain,(
    ! [B_65] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_65))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_65))
      | ~ v1_relat_1(B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_26])).

tff(c_199,plain,(
    ! [B_66] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_66))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_66))
      | ~ v1_relat_1(B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_191])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_204,plain,(
    ! [B_67] :
      ( k5_relat_1(k1_xboole_0,B_67) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_67))
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_199,c_4])).

tff(c_208,plain,(
    ! [B_27] :
      ( k5_relat_1(k1_xboole_0,B_27) = k1_xboole_0
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_204])).

tff(c_216,plain,(
    ! [B_70] :
      ( k5_relat_1(k1_xboole_0,B_70) = k1_xboole_0
      | ~ v1_relat_1(B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_208])).

tff(c_231,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_216])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_231])).

tff(c_240,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_1'(A_7),A_7)
      | v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_246,plain,(
    ! [A_71,B_72] : ~ r2_hidden(A_71,k2_zfmisc_1(A_71,B_72)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_254,plain,(
    ! [A_74] : ~ r2_hidden(A_74,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_246])).

tff(c_259,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_254])).

tff(c_22,plain,(
    ! [A_25] :
      ( v1_relat_1(k4_relat_1(A_25))
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_332,plain,(
    ! [A_88,B_89] :
      ( k1_relat_1(k5_relat_1(A_88,B_89)) = k1_relat_1(A_88)
      | ~ r1_tarski(k2_relat_1(A_88),k1_relat_1(B_89))
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_338,plain,(
    ! [B_89] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_89)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_89))
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_332])).

tff(c_343,plain,(
    ! [B_90] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_90)) = k1_xboole_0
      | ~ v1_relat_1(B_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_6,c_36,c_338])).

tff(c_352,plain,(
    ! [B_90] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_90))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_90))
      | ~ v1_relat_1(B_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_26])).

tff(c_384,plain,(
    ! [B_98] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_98))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_98))
      | ~ v1_relat_1(B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_352])).

tff(c_394,plain,(
    ! [B_99] :
      ( k5_relat_1(k1_xboole_0,B_99) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_99))
      | ~ v1_relat_1(B_99) ) ),
    inference(resolution,[status(thm)],[c_384,c_4])).

tff(c_398,plain,(
    ! [B_27] :
      ( k5_relat_1(k1_xboole_0,B_27) = k1_xboole_0
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_394])).

tff(c_407,plain,(
    ! [B_100] :
      ( k5_relat_1(k1_xboole_0,B_100) = k1_xboole_0
      | ~ v1_relat_1(B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_398])).

tff(c_426,plain,(
    ! [A_25] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_25)) = k1_xboole_0
      | ~ v1_relat_1(A_25) ) ),
    inference(resolution,[status(thm)],[c_22,c_407])).

tff(c_28,plain,(
    ! [A_29] :
      ( k4_relat_1(k4_relat_1(A_29)) = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_304,plain,(
    ! [B_84,A_85] :
      ( k5_relat_1(k4_relat_1(B_84),k4_relat_1(A_85)) = k4_relat_1(k5_relat_1(A_85,B_84))
      | ~ v1_relat_1(B_84)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_583,plain,(
    ! [A_107,A_108] :
      ( k4_relat_1(k5_relat_1(A_107,k4_relat_1(A_108))) = k5_relat_1(A_108,k4_relat_1(A_107))
      | ~ v1_relat_1(k4_relat_1(A_108))
      | ~ v1_relat_1(A_107)
      | ~ v1_relat_1(A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_304])).

tff(c_630,plain,(
    ! [A_25] :
      ( k5_relat_1(A_25,k4_relat_1(k1_xboole_0)) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_25))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_583])).

tff(c_680,plain,(
    ! [A_112] :
      ( k5_relat_1(A_112,k4_relat_1(k1_xboole_0)) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_112))
      | ~ v1_relat_1(A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_630])).

tff(c_698,plain,(
    ! [A_113] :
      ( k5_relat_1(A_113,k4_relat_1(k1_xboole_0)) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_113) ) ),
    inference(resolution,[status(thm)],[c_22,c_680])).

tff(c_720,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_698,c_426])).

tff(c_756,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_259,c_720])).

tff(c_697,plain,(
    ! [A_25] :
      ( k5_relat_1(A_25,k4_relat_1(k1_xboole_0)) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_25) ) ),
    inference(resolution,[status(thm)],[c_22,c_680])).

tff(c_831,plain,(
    ! [A_116] :
      ( k5_relat_1(A_116,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_756,c_756,c_697])).

tff(c_846,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_831])).

tff(c_855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_846])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.44  
% 2.49/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.45  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.49/1.45  
% 2.49/1.45  %Foreground sorts:
% 2.49/1.45  
% 2.49/1.45  
% 2.49/1.45  %Background operators:
% 2.49/1.45  
% 2.49/1.45  
% 2.49/1.45  %Foreground operators:
% 2.49/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.49/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.49/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.49/1.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.49/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.49/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.49/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.49/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.45  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.49/1.45  
% 2.93/1.46  tff(f_99, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.93/1.46  tff(f_51, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.93/1.46  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.93/1.46  tff(f_41, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.93/1.46  tff(f_61, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.93/1.46  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.93/1.46  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.93/1.46  tff(f_92, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.93/1.46  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.93/1.46  tff(f_69, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.93/1.46  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.93/1.46  tff(f_55, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.93/1.46  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 2.93/1.46  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 2.93/1.46  tff(c_38, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.93/1.46  tff(c_79, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 2.93/1.46  tff(c_40, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.93/1.46  tff(c_88, plain, (![A_44]: (r2_hidden('#skF_1'(A_44), A_44) | v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.93/1.46  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.93/1.46  tff(c_80, plain, (![A_41, B_42]: (~r2_hidden(A_41, k2_zfmisc_1(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.93/1.46  tff(c_86, plain, (![A_3]: (~r2_hidden(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_80])).
% 2.93/1.46  tff(c_93, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_88, c_86])).
% 2.93/1.46  tff(c_24, plain, (![A_26, B_27]: (v1_relat_1(k5_relat_1(A_26, B_27)) | ~v1_relat_1(B_27) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.93/1.46  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.93/1.46  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.93/1.46  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.93/1.46  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.93/1.46  tff(c_171, plain, (![A_63, B_64]: (k1_relat_1(k5_relat_1(A_63, B_64))=k1_relat_1(A_63) | ~r1_tarski(k2_relat_1(A_63), k1_relat_1(B_64)) | ~v1_relat_1(B_64) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.93/1.46  tff(c_177, plain, (![B_64]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_64))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_64)) | ~v1_relat_1(B_64) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_171])).
% 2.93/1.46  tff(c_182, plain, (![B_65]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_65))=k1_xboole_0 | ~v1_relat_1(B_65))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_6, c_36, c_177])).
% 2.93/1.46  tff(c_26, plain, (![A_28]: (~v1_xboole_0(k1_relat_1(A_28)) | ~v1_relat_1(A_28) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.93/1.46  tff(c_191, plain, (![B_65]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_65)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_65)) | ~v1_relat_1(B_65))), inference(superposition, [status(thm), theory('equality')], [c_182, c_26])).
% 2.93/1.46  tff(c_199, plain, (![B_66]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_66)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_66)) | ~v1_relat_1(B_66))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_191])).
% 2.93/1.46  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.93/1.46  tff(c_204, plain, (![B_67]: (k5_relat_1(k1_xboole_0, B_67)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_67)) | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_199, c_4])).
% 2.93/1.46  tff(c_208, plain, (![B_27]: (k5_relat_1(k1_xboole_0, B_27)=k1_xboole_0 | ~v1_relat_1(B_27) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_204])).
% 2.93/1.46  tff(c_216, plain, (![B_70]: (k5_relat_1(k1_xboole_0, B_70)=k1_xboole_0 | ~v1_relat_1(B_70))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_208])).
% 2.93/1.46  tff(c_231, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_216])).
% 2.93/1.46  tff(c_239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_231])).
% 2.93/1.46  tff(c_240, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 2.93/1.46  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_1'(A_7), A_7) | v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.93/1.46  tff(c_246, plain, (![A_71, B_72]: (~r2_hidden(A_71, k2_zfmisc_1(A_71, B_72)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.93/1.46  tff(c_254, plain, (![A_74]: (~r2_hidden(A_74, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_246])).
% 2.93/1.46  tff(c_259, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_254])).
% 2.93/1.46  tff(c_22, plain, (![A_25]: (v1_relat_1(k4_relat_1(A_25)) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.93/1.46  tff(c_332, plain, (![A_88, B_89]: (k1_relat_1(k5_relat_1(A_88, B_89))=k1_relat_1(A_88) | ~r1_tarski(k2_relat_1(A_88), k1_relat_1(B_89)) | ~v1_relat_1(B_89) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.93/1.46  tff(c_338, plain, (![B_89]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_89))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_89)) | ~v1_relat_1(B_89) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_332])).
% 2.93/1.46  tff(c_343, plain, (![B_90]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_90))=k1_xboole_0 | ~v1_relat_1(B_90))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_6, c_36, c_338])).
% 2.93/1.46  tff(c_352, plain, (![B_90]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_90)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_90)) | ~v1_relat_1(B_90))), inference(superposition, [status(thm), theory('equality')], [c_343, c_26])).
% 2.93/1.46  tff(c_384, plain, (![B_98]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_98)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_98)) | ~v1_relat_1(B_98))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_352])).
% 2.93/1.46  tff(c_394, plain, (![B_99]: (k5_relat_1(k1_xboole_0, B_99)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_99)) | ~v1_relat_1(B_99))), inference(resolution, [status(thm)], [c_384, c_4])).
% 2.93/1.46  tff(c_398, plain, (![B_27]: (k5_relat_1(k1_xboole_0, B_27)=k1_xboole_0 | ~v1_relat_1(B_27) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_394])).
% 2.93/1.46  tff(c_407, plain, (![B_100]: (k5_relat_1(k1_xboole_0, B_100)=k1_xboole_0 | ~v1_relat_1(B_100))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_398])).
% 2.93/1.46  tff(c_426, plain, (![A_25]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_25))=k1_xboole_0 | ~v1_relat_1(A_25))), inference(resolution, [status(thm)], [c_22, c_407])).
% 2.93/1.46  tff(c_28, plain, (![A_29]: (k4_relat_1(k4_relat_1(A_29))=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.93/1.46  tff(c_304, plain, (![B_84, A_85]: (k5_relat_1(k4_relat_1(B_84), k4_relat_1(A_85))=k4_relat_1(k5_relat_1(A_85, B_84)) | ~v1_relat_1(B_84) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.93/1.46  tff(c_583, plain, (![A_107, A_108]: (k4_relat_1(k5_relat_1(A_107, k4_relat_1(A_108)))=k5_relat_1(A_108, k4_relat_1(A_107)) | ~v1_relat_1(k4_relat_1(A_108)) | ~v1_relat_1(A_107) | ~v1_relat_1(A_108))), inference(superposition, [status(thm), theory('equality')], [c_28, c_304])).
% 2.93/1.46  tff(c_630, plain, (![A_25]: (k5_relat_1(A_25, k4_relat_1(k1_xboole_0))=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_25)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_25) | ~v1_relat_1(A_25))), inference(superposition, [status(thm), theory('equality')], [c_426, c_583])).
% 2.93/1.46  tff(c_680, plain, (![A_112]: (k5_relat_1(A_112, k4_relat_1(k1_xboole_0))=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_112)) | ~v1_relat_1(A_112))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_630])).
% 2.93/1.46  tff(c_698, plain, (![A_113]: (k5_relat_1(A_113, k4_relat_1(k1_xboole_0))=k4_relat_1(k1_xboole_0) | ~v1_relat_1(A_113))), inference(resolution, [status(thm)], [c_22, c_680])).
% 2.93/1.46  tff(c_720, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_698, c_426])).
% 2.93/1.46  tff(c_756, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_259, c_259, c_720])).
% 2.93/1.46  tff(c_697, plain, (![A_25]: (k5_relat_1(A_25, k4_relat_1(k1_xboole_0))=k4_relat_1(k1_xboole_0) | ~v1_relat_1(A_25))), inference(resolution, [status(thm)], [c_22, c_680])).
% 2.93/1.46  tff(c_831, plain, (![A_116]: (k5_relat_1(A_116, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_116))), inference(demodulation, [status(thm), theory('equality')], [c_756, c_756, c_697])).
% 2.93/1.46  tff(c_846, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_831])).
% 2.93/1.46  tff(c_855, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_846])).
% 2.93/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.46  
% 2.93/1.46  Inference rules
% 2.93/1.46  ----------------------
% 2.93/1.46  #Ref     : 2
% 2.93/1.46  #Sup     : 192
% 2.93/1.46  #Fact    : 0
% 2.93/1.46  #Define  : 0
% 2.93/1.46  #Split   : 1
% 2.93/1.46  #Chain   : 0
% 2.93/1.46  #Close   : 0
% 2.93/1.46  
% 2.93/1.46  Ordering : KBO
% 2.93/1.46  
% 2.93/1.46  Simplification rules
% 2.93/1.46  ----------------------
% 2.93/1.46  #Subsume      : 12
% 2.93/1.46  #Demod        : 114
% 2.93/1.46  #Tautology    : 88
% 2.93/1.46  #SimpNegUnit  : 2
% 2.93/1.46  #BackRed      : 2
% 2.93/1.46  
% 2.93/1.46  #Partial instantiations: 0
% 2.93/1.46  #Strategies tried      : 1
% 2.93/1.46  
% 2.93/1.46  Timing (in seconds)
% 2.93/1.46  ----------------------
% 2.93/1.47  Preprocessing        : 0.28
% 2.93/1.47  Parsing              : 0.15
% 2.93/1.47  CNF conversion       : 0.02
% 2.93/1.47  Main loop            : 0.35
% 2.93/1.47  Inferencing          : 0.14
% 2.93/1.47  Reduction            : 0.09
% 2.93/1.47  Demodulation         : 0.06
% 2.93/1.47  BG Simplification    : 0.02
% 2.93/1.47  Subsumption          : 0.07
% 2.93/1.47  Abstraction          : 0.02
% 2.93/1.47  MUC search           : 0.00
% 2.93/1.47  Cooper               : 0.00
% 2.93/1.47  Total                : 0.66
% 2.93/1.47  Index Insertion      : 0.00
% 2.93/1.47  Index Deletion       : 0.00
% 2.93/1.47  Index Matching       : 0.00
% 2.93/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
