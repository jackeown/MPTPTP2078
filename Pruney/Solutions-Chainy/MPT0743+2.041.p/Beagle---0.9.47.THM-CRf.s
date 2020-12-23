%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:13 EST 2020

% Result     : Theorem 5.39s
% Output     : CNFRefutation 5.40s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 147 expanded)
%              Number of leaves         :   28 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  171 ( 335 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_76,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_72,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_62,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_40,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_38,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_24,plain,(
    ! [B_24,A_23] :
      ( r1_ordinal1(B_24,A_23)
      | r1_ordinal1(A_23,B_24)
      | ~ v3_ordinal1(B_24)
      | ~ v3_ordinal1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_636,plain,(
    ! [B_24] :
      ( ~ v3_ordinal1(B_24)
      | r1_ordinal1(B_24,B_24) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_24])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ r1_ordinal1(A_26,B_27)
      | ~ v3_ordinal1(B_27)
      | ~ v3_ordinal1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_652,plain,(
    ! [A_139,B_140] :
      ( r1_tarski(A_139,B_140)
      | ~ r1_ordinal1(A_139,B_140)
      | ~ v3_ordinal1(B_140)
      | ~ v3_ordinal1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,(
    ! [A_29] :
      ( v3_ordinal1(k1_ordinal1(A_29))
      | ~ v3_ordinal1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_48,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_76,plain,(
    r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_42,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_87,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_42])).

tff(c_199,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(A_70,B_71)
      | ~ r1_ordinal1(A_70,B_71)
      | ~ v3_ordinal1(B_71)
      | ~ v3_ordinal1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_32,plain,(
    ! [A_28] : r2_hidden(A_28,k1_ordinal1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_139,plain,(
    ! [C_54,B_55,A_56] :
      ( r2_hidden(C_54,B_55)
      | ~ r2_hidden(C_54,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_145,plain,(
    ! [A_28,B_55] :
      ( r2_hidden(A_28,B_55)
      | ~ r1_tarski(k1_ordinal1(A_28),B_55) ) ),
    inference(resolution,[status(thm)],[c_32,c_139])).

tff(c_438,plain,(
    ! [A_104,B_105] :
      ( r2_hidden(A_104,B_105)
      | ~ r1_ordinal1(k1_ordinal1(A_104),B_105)
      | ~ v3_ordinal1(B_105)
      | ~ v3_ordinal1(k1_ordinal1(A_104)) ) ),
    inference(resolution,[status(thm)],[c_199,c_145])).

tff(c_461,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_438])).

tff(c_470,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_461])).

tff(c_471,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_470])).

tff(c_474,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_471])).

tff(c_478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_474])).

tff(c_479,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_574,plain,(
    ! [C_126,B_127,A_128] :
      ( r2_hidden(C_126,B_127)
      | ~ r2_hidden(C_126,A_128)
      | ~ r1_tarski(A_128,B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_587,plain,(
    ! [B_129] :
      ( r2_hidden('#skF_2',B_129)
      | ~ r1_tarski('#skF_3',B_129) ) ),
    inference(resolution,[status(thm)],[c_479,c_574])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_597,plain,(
    ! [B_2,B_129] :
      ( r2_hidden('#skF_2',B_2)
      | ~ r1_tarski(B_129,B_2)
      | ~ r1_tarski('#skF_3',B_129) ) ),
    inference(resolution,[status(thm)],[c_587,c_2])).

tff(c_1229,plain,(
    ! [B_203,A_204] :
      ( r2_hidden('#skF_2',B_203)
      | ~ r1_tarski('#skF_3',A_204)
      | ~ r1_ordinal1(A_204,B_203)
      | ~ v3_ordinal1(B_203)
      | ~ v3_ordinal1(A_204) ) ),
    inference(resolution,[status(thm)],[c_652,c_597])).

tff(c_1232,plain,(
    ! [B_203,B_27] :
      ( r2_hidden('#skF_2',B_203)
      | ~ r1_ordinal1(B_27,B_203)
      | ~ v3_ordinal1(B_203)
      | ~ r1_ordinal1('#skF_3',B_27)
      | ~ v3_ordinal1(B_27)
      | ~ v3_ordinal1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_1229])).

tff(c_1777,plain,(
    ! [B_255,B_256] :
      ( r2_hidden('#skF_2',B_255)
      | ~ r1_ordinal1(B_256,B_255)
      | ~ v3_ordinal1(B_255)
      | ~ r1_ordinal1('#skF_3',B_256)
      | ~ v3_ordinal1(B_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1232])).

tff(c_2125,plain,(
    ! [B_283,A_284] :
      ( r2_hidden('#skF_2',B_283)
      | ~ r1_ordinal1('#skF_3',A_284)
      | r1_ordinal1(B_283,A_284)
      | ~ v3_ordinal1(B_283)
      | ~ v3_ordinal1(A_284) ) ),
    inference(resolution,[status(thm)],[c_24,c_1777])).

tff(c_2142,plain,(
    ! [B_283] :
      ( r2_hidden('#skF_2',B_283)
      | r1_ordinal1(B_283,'#skF_3')
      | ~ v3_ordinal1(B_283)
      | ~ v3_ordinal1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_636,c_2125])).

tff(c_2180,plain,(
    ! [B_286] :
      ( r2_hidden('#skF_2',B_286)
      | r1_ordinal1(B_286,'#skF_3')
      | ~ v3_ordinal1(B_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2142])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(k1_tarski(A_19),B_20)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_531,plain,(
    ! [A_115,B_116] :
      ( r2_hidden('#skF_1'(A_115,B_116),A_115)
      | r1_tarski(A_115,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_541,plain,(
    ! [A_117] : r1_tarski(A_117,A_117) ),
    inference(resolution,[status(thm)],[c_531,c_4])).

tff(c_18,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | ~ r1_tarski(k1_tarski(A_19),B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_547,plain,(
    ! [A_118] : r2_hidden(A_118,k1_tarski(A_118)) ),
    inference(resolution,[status(thm)],[c_541,c_18])).

tff(c_36,plain,(
    ! [B_31,A_30] :
      ( ~ r1_tarski(B_31,A_30)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_552,plain,(
    ! [A_119] : ~ r1_tarski(k1_tarski(A_119),A_119) ),
    inference(resolution,[status(thm)],[c_547,c_36])).

tff(c_557,plain,(
    ! [B_20] : ~ r2_hidden(B_20,B_20) ),
    inference(resolution,[status(thm)],[c_20,c_552])).

tff(c_2200,plain,
    ( r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2180,c_557])).

tff(c_2213,plain,(
    r1_ordinal1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2200])).

tff(c_638,plain,(
    ! [B_136,A_137] :
      ( r1_ordinal1(B_136,A_137)
      | r1_ordinal1(A_137,B_136)
      | ~ v3_ordinal1(B_136)
      | ~ v3_ordinal1(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_480,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_641,plain,
    ( r1_ordinal1('#skF_3',k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_638,c_480])).

tff(c_647,plain,
    ( r1_ordinal1('#skF_3',k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_641])).

tff(c_701,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_647])).

tff(c_704,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_701])).

tff(c_708,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_704])).

tff(c_710,plain,(
    v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_647])).

tff(c_26,plain,(
    ! [A_25] : k2_xboole_0(A_25,k1_tarski(A_25)) = k1_ordinal1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_791,plain,(
    ! [A_150,C_151,B_152] :
      ( r1_tarski(k2_xboole_0(A_150,C_151),B_152)
      | ~ r1_tarski(C_151,B_152)
      | ~ r1_tarski(A_150,B_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_895,plain,(
    ! [A_168,B_169] :
      ( r1_tarski(k1_ordinal1(A_168),B_169)
      | ~ r1_tarski(k1_tarski(A_168),B_169)
      | ~ r1_tarski(A_168,B_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_791])).

tff(c_936,plain,(
    ! [A_172,B_173] :
      ( r1_tarski(k1_ordinal1(A_172),B_173)
      | ~ r1_tarski(A_172,B_173)
      | ~ r2_hidden(A_172,B_173) ) ),
    inference(resolution,[status(thm)],[c_20,c_895])).

tff(c_28,plain,(
    ! [A_26,B_27] :
      ( r1_ordinal1(A_26,B_27)
      | ~ r1_tarski(A_26,B_27)
      | ~ v3_ordinal1(B_27)
      | ~ v3_ordinal1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2919,plain,(
    ! [A_315,B_316] :
      ( r1_ordinal1(k1_ordinal1(A_315),B_316)
      | ~ v3_ordinal1(B_316)
      | ~ v3_ordinal1(k1_ordinal1(A_315))
      | ~ r1_tarski(A_315,B_316)
      | ~ r2_hidden(A_315,B_316) ) ),
    inference(resolution,[status(thm)],[c_936,c_28])).

tff(c_2953,plain,
    ( ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_2919,c_480])).

tff(c_2977,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_710,c_38,c_2953])).

tff(c_2980,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_2977])).

tff(c_2984,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2213,c_2980])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:50:46 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.39/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.40/2.08  
% 5.40/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.40/2.08  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1
% 5.40/2.08  
% 5.40/2.08  %Foreground sorts:
% 5.40/2.08  
% 5.40/2.08  
% 5.40/2.08  %Background operators:
% 5.40/2.08  
% 5.40/2.08  
% 5.40/2.08  %Foreground operators:
% 5.40/2.08  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 5.40/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.40/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.40/2.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.40/2.08  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.40/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.40/2.08  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.40/2.08  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 5.40/2.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.40/2.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.40/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.40/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.40/2.08  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 5.40/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.40/2.08  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.40/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.40/2.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.40/2.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.40/2.08  
% 5.40/2.10  tff(f_91, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 5.40/2.10  tff(f_60, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 5.40/2.10  tff(f_70, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 5.40/2.10  tff(f_76, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 5.40/2.10  tff(f_72, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 5.40/2.10  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.40/2.10  tff(f_50, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.40/2.10  tff(f_81, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.40/2.10  tff(f_62, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 5.40/2.10  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 5.40/2.10  tff(c_40, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.40/2.10  tff(c_38, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.40/2.10  tff(c_24, plain, (![B_24, A_23]: (r1_ordinal1(B_24, A_23) | r1_ordinal1(A_23, B_24) | ~v3_ordinal1(B_24) | ~v3_ordinal1(A_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.40/2.10  tff(c_636, plain, (![B_24]: (~v3_ordinal1(B_24) | r1_ordinal1(B_24, B_24))), inference(factorization, [status(thm), theory('equality')], [c_24])).
% 5.40/2.10  tff(c_30, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~r1_ordinal1(A_26, B_27) | ~v3_ordinal1(B_27) | ~v3_ordinal1(A_26))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.40/2.10  tff(c_652, plain, (![A_139, B_140]: (r1_tarski(A_139, B_140) | ~r1_ordinal1(A_139, B_140) | ~v3_ordinal1(B_140) | ~v3_ordinal1(A_139))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.40/2.10  tff(c_34, plain, (![A_29]: (v3_ordinal1(k1_ordinal1(A_29)) | ~v3_ordinal1(A_29))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.40/2.10  tff(c_48, plain, (r2_hidden('#skF_2', '#skF_3') | r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.40/2.10  tff(c_76, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 5.40/2.10  tff(c_42, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3') | ~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.40/2.10  tff(c_87, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_42])).
% 5.40/2.10  tff(c_199, plain, (![A_70, B_71]: (r1_tarski(A_70, B_71) | ~r1_ordinal1(A_70, B_71) | ~v3_ordinal1(B_71) | ~v3_ordinal1(A_70))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.40/2.10  tff(c_32, plain, (![A_28]: (r2_hidden(A_28, k1_ordinal1(A_28)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.40/2.10  tff(c_139, plain, (![C_54, B_55, A_56]: (r2_hidden(C_54, B_55) | ~r2_hidden(C_54, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.40/2.10  tff(c_145, plain, (![A_28, B_55]: (r2_hidden(A_28, B_55) | ~r1_tarski(k1_ordinal1(A_28), B_55))), inference(resolution, [status(thm)], [c_32, c_139])).
% 5.40/2.10  tff(c_438, plain, (![A_104, B_105]: (r2_hidden(A_104, B_105) | ~r1_ordinal1(k1_ordinal1(A_104), B_105) | ~v3_ordinal1(B_105) | ~v3_ordinal1(k1_ordinal1(A_104)))), inference(resolution, [status(thm)], [c_199, c_145])).
% 5.40/2.10  tff(c_461, plain, (r2_hidden('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_76, c_438])).
% 5.40/2.10  tff(c_470, plain, (r2_hidden('#skF_2', '#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_461])).
% 5.40/2.10  tff(c_471, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_87, c_470])).
% 5.40/2.10  tff(c_474, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_471])).
% 5.40/2.10  tff(c_478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_474])).
% 5.40/2.10  tff(c_479, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 5.40/2.10  tff(c_574, plain, (![C_126, B_127, A_128]: (r2_hidden(C_126, B_127) | ~r2_hidden(C_126, A_128) | ~r1_tarski(A_128, B_127))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.40/2.10  tff(c_587, plain, (![B_129]: (r2_hidden('#skF_2', B_129) | ~r1_tarski('#skF_3', B_129))), inference(resolution, [status(thm)], [c_479, c_574])).
% 5.40/2.10  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.40/2.10  tff(c_597, plain, (![B_2, B_129]: (r2_hidden('#skF_2', B_2) | ~r1_tarski(B_129, B_2) | ~r1_tarski('#skF_3', B_129))), inference(resolution, [status(thm)], [c_587, c_2])).
% 5.40/2.10  tff(c_1229, plain, (![B_203, A_204]: (r2_hidden('#skF_2', B_203) | ~r1_tarski('#skF_3', A_204) | ~r1_ordinal1(A_204, B_203) | ~v3_ordinal1(B_203) | ~v3_ordinal1(A_204))), inference(resolution, [status(thm)], [c_652, c_597])).
% 5.40/2.10  tff(c_1232, plain, (![B_203, B_27]: (r2_hidden('#skF_2', B_203) | ~r1_ordinal1(B_27, B_203) | ~v3_ordinal1(B_203) | ~r1_ordinal1('#skF_3', B_27) | ~v3_ordinal1(B_27) | ~v3_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_1229])).
% 5.40/2.10  tff(c_1777, plain, (![B_255, B_256]: (r2_hidden('#skF_2', B_255) | ~r1_ordinal1(B_256, B_255) | ~v3_ordinal1(B_255) | ~r1_ordinal1('#skF_3', B_256) | ~v3_ordinal1(B_256))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1232])).
% 5.40/2.10  tff(c_2125, plain, (![B_283, A_284]: (r2_hidden('#skF_2', B_283) | ~r1_ordinal1('#skF_3', A_284) | r1_ordinal1(B_283, A_284) | ~v3_ordinal1(B_283) | ~v3_ordinal1(A_284))), inference(resolution, [status(thm)], [c_24, c_1777])).
% 5.40/2.10  tff(c_2142, plain, (![B_283]: (r2_hidden('#skF_2', B_283) | r1_ordinal1(B_283, '#skF_3') | ~v3_ordinal1(B_283) | ~v3_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_636, c_2125])).
% 5.40/2.10  tff(c_2180, plain, (![B_286]: (r2_hidden('#skF_2', B_286) | r1_ordinal1(B_286, '#skF_3') | ~v3_ordinal1(B_286))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2142])).
% 5.40/2.10  tff(c_20, plain, (![A_19, B_20]: (r1_tarski(k1_tarski(A_19), B_20) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.40/2.10  tff(c_531, plain, (![A_115, B_116]: (r2_hidden('#skF_1'(A_115, B_116), A_115) | r1_tarski(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.40/2.10  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.40/2.10  tff(c_541, plain, (![A_117]: (r1_tarski(A_117, A_117))), inference(resolution, [status(thm)], [c_531, c_4])).
% 5.40/2.10  tff(c_18, plain, (![A_19, B_20]: (r2_hidden(A_19, B_20) | ~r1_tarski(k1_tarski(A_19), B_20))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.40/2.10  tff(c_547, plain, (![A_118]: (r2_hidden(A_118, k1_tarski(A_118)))), inference(resolution, [status(thm)], [c_541, c_18])).
% 5.40/2.10  tff(c_36, plain, (![B_31, A_30]: (~r1_tarski(B_31, A_30) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.40/2.10  tff(c_552, plain, (![A_119]: (~r1_tarski(k1_tarski(A_119), A_119))), inference(resolution, [status(thm)], [c_547, c_36])).
% 5.40/2.10  tff(c_557, plain, (![B_20]: (~r2_hidden(B_20, B_20))), inference(resolution, [status(thm)], [c_20, c_552])).
% 5.40/2.10  tff(c_2200, plain, (r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_2180, c_557])).
% 5.40/2.10  tff(c_2213, plain, (r1_ordinal1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2200])).
% 5.40/2.10  tff(c_638, plain, (![B_136, A_137]: (r1_ordinal1(B_136, A_137) | r1_ordinal1(A_137, B_136) | ~v3_ordinal1(B_136) | ~v3_ordinal1(A_137))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.40/2.10  tff(c_480, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 5.40/2.10  tff(c_641, plain, (r1_ordinal1('#skF_3', k1_ordinal1('#skF_2')) | ~v3_ordinal1(k1_ordinal1('#skF_2')) | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_638, c_480])).
% 5.40/2.10  tff(c_647, plain, (r1_ordinal1('#skF_3', k1_ordinal1('#skF_2')) | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_641])).
% 5.40/2.10  tff(c_701, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_647])).
% 5.40/2.10  tff(c_704, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_701])).
% 5.40/2.10  tff(c_708, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_704])).
% 5.40/2.10  tff(c_710, plain, (v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_647])).
% 5.40/2.10  tff(c_26, plain, (![A_25]: (k2_xboole_0(A_25, k1_tarski(A_25))=k1_ordinal1(A_25))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.40/2.10  tff(c_791, plain, (![A_150, C_151, B_152]: (r1_tarski(k2_xboole_0(A_150, C_151), B_152) | ~r1_tarski(C_151, B_152) | ~r1_tarski(A_150, B_152))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.40/2.10  tff(c_895, plain, (![A_168, B_169]: (r1_tarski(k1_ordinal1(A_168), B_169) | ~r1_tarski(k1_tarski(A_168), B_169) | ~r1_tarski(A_168, B_169))), inference(superposition, [status(thm), theory('equality')], [c_26, c_791])).
% 5.40/2.10  tff(c_936, plain, (![A_172, B_173]: (r1_tarski(k1_ordinal1(A_172), B_173) | ~r1_tarski(A_172, B_173) | ~r2_hidden(A_172, B_173))), inference(resolution, [status(thm)], [c_20, c_895])).
% 5.40/2.10  tff(c_28, plain, (![A_26, B_27]: (r1_ordinal1(A_26, B_27) | ~r1_tarski(A_26, B_27) | ~v3_ordinal1(B_27) | ~v3_ordinal1(A_26))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.40/2.10  tff(c_2919, plain, (![A_315, B_316]: (r1_ordinal1(k1_ordinal1(A_315), B_316) | ~v3_ordinal1(B_316) | ~v3_ordinal1(k1_ordinal1(A_315)) | ~r1_tarski(A_315, B_316) | ~r2_hidden(A_315, B_316))), inference(resolution, [status(thm)], [c_936, c_28])).
% 5.40/2.10  tff(c_2953, plain, (~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2')) | ~r1_tarski('#skF_2', '#skF_3') | ~r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_2919, c_480])).
% 5.40/2.10  tff(c_2977, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_479, c_710, c_38, c_2953])).
% 5.40/2.10  tff(c_2980, plain, (~r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_2977])).
% 5.40/2.10  tff(c_2984, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_2213, c_2980])).
% 5.40/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.40/2.10  
% 5.40/2.10  Inference rules
% 5.40/2.10  ----------------------
% 5.40/2.10  #Ref     : 0
% 5.40/2.10  #Sup     : 563
% 5.40/2.10  #Fact    : 8
% 5.40/2.10  #Define  : 0
% 5.40/2.10  #Split   : 9
% 5.40/2.10  #Chain   : 0
% 5.40/2.10  #Close   : 0
% 5.40/2.10  
% 5.40/2.10  Ordering : KBO
% 5.40/2.10  
% 5.40/2.10  Simplification rules
% 5.40/2.10  ----------------------
% 5.40/2.10  #Subsume      : 137
% 5.40/2.10  #Demod        : 255
% 5.40/2.10  #Tautology    : 67
% 5.40/2.10  #SimpNegUnit  : 2
% 5.40/2.10  #BackRed      : 0
% 5.40/2.10  
% 5.40/2.10  #Partial instantiations: 0
% 5.40/2.10  #Strategies tried      : 1
% 5.40/2.10  
% 5.40/2.10  Timing (in seconds)
% 5.40/2.10  ----------------------
% 5.53/2.10  Preprocessing        : 0.31
% 5.53/2.10  Parsing              : 0.17
% 5.53/2.10  CNF conversion       : 0.02
% 5.53/2.10  Main loop            : 0.97
% 5.53/2.10  Inferencing          : 0.34
% 5.53/2.10  Reduction            : 0.28
% 5.53/2.10  Demodulation         : 0.18
% 5.53/2.10  BG Simplification    : 0.03
% 5.53/2.10  Subsumption          : 0.25
% 5.53/2.10  Abstraction          : 0.04
% 5.53/2.10  MUC search           : 0.00
% 5.53/2.10  Cooper               : 0.00
% 5.53/2.10  Total                : 1.31
% 5.53/2.10  Index Insertion      : 0.00
% 5.53/2.10  Index Deletion       : 0.00
% 5.53/2.10  Index Matching       : 0.00
% 5.53/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
