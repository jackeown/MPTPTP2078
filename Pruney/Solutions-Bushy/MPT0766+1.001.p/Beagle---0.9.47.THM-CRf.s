%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0766+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:49 EST 2020

% Result     : Theorem 4.56s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 115 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 402 expanded)
%              Number of equality atoms :   11 (  37 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v2_wellord1 > v1_xboole_0 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_25,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_33,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( v2_wellord1(A)
         => ! [B] :
              ~ ( r2_hidden(B,k3_relat_1(A))
                & ? [C] :
                    ( r2_hidden(C,k3_relat_1(A))
                    & ~ r2_hidden(k4_tarski(C,B),A) )
                & ! [C] :
                    ~ ( r2_hidden(C,k3_relat_1(A))
                      & r2_hidden(k4_tarski(B,C),A)
                      & ! [D] :
                          ~ ( r2_hidden(D,k3_relat_1(A))
                            & r2_hidden(k4_tarski(B,D),A)
                            & D != B
                            & ~ r2_hidden(k4_tarski(C,D),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_wellord1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => ? [C] :
        ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,k3_relat_1(A))
            & ~ r2_hidden(k4_tarski(D,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e7_18__wellord1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r1_tarski(B,k3_relat_1(A))
              & B != k1_xboole_0
              & ! [C] :
                  ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( r2_hidden(D,B)
                       => r2_hidden(k4_tarski(C,D),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord1)).

tff(f_73,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(c_2,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_25])).

tff(c_10,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_121,plain,(
    ! [D_66,A_67,B_68] :
      ( r2_hidden(D_66,k3_relat_1(A_67))
      | ~ r2_hidden(D_66,'#skF_2'(A_67,B_68))
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_598,plain,(
    ! [A_119,B_120,B_121] :
      ( r2_hidden('#skF_1'('#skF_2'(A_119,B_120),B_121),k3_relat_1(A_119))
      | ~ v1_relat_1(A_119)
      | r1_tarski('#skF_2'(A_119,B_120),B_121) ) ),
    inference(resolution,[status(thm)],[c_8,c_121])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_621,plain,(
    ! [A_119,B_120] :
      ( ~ v1_relat_1(A_119)
      | r1_tarski('#skF_2'(A_119,B_120),k3_relat_1(A_119)) ) ),
    inference(resolution,[status(thm)],[c_598,c_6])).

tff(c_34,plain,(
    v2_wellord1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32,plain,(
    r2_hidden('#skF_5',k3_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_223,plain,(
    ! [D_90,A_91,B_92] :
      ( r2_hidden(D_90,'#skF_2'(A_91,B_92))
      | r2_hidden(k4_tarski(D_90,B_92),A_91)
      | ~ r2_hidden(D_90,k3_relat_1(A_91))
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_42,plain,(
    ! [C_44] :
      ( r2_hidden(k4_tarski('#skF_5','#skF_7'(C_44)),'#skF_4')
      | ~ r2_hidden(k4_tarski('#skF_5',C_44),'#skF_4')
      | ~ r2_hidden(C_44,k3_relat_1('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_215,plain,(
    ! [C_89] :
      ( ~ r2_hidden(k4_tarski(C_89,'#skF_7'(C_89)),'#skF_4')
      | ~ r2_hidden(k4_tarski('#skF_5',C_89),'#skF_4')
      | ~ r2_hidden(C_89,k3_relat_1('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_219,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_5',k3_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_215])).

tff(c_222,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_219])).

tff(c_226,plain,
    ( r2_hidden('#skF_5','#skF_2'('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_5',k3_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_223,c_222])).

tff(c_251,plain,(
    r2_hidden('#skF_5','#skF_2'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_226])).

tff(c_20,plain,(
    ! [A_13,B_21] :
      ( r2_hidden('#skF_3'(A_13,B_21),B_21)
      | k1_xboole_0 = B_21
      | ~ r1_tarski(B_21,k3_relat_1(A_13))
      | ~ v2_wellord1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_351,plain,(
    ! [A_98,B_99,D_100] :
      ( r2_hidden(k4_tarski('#skF_3'(A_98,B_99),D_100),A_98)
      | ~ r2_hidden(D_100,B_99)
      | k1_xboole_0 = B_99
      | ~ r1_tarski(B_99,k3_relat_1(A_98))
      | ~ v2_wellord1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [D_12,B_7,A_6] :
      ( ~ r2_hidden(k4_tarski(D_12,B_7),A_6)
      | ~ r2_hidden(D_12,'#skF_2'(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_989,plain,(
    ! [A_165,B_166,D_167] :
      ( ~ r2_hidden('#skF_3'(A_165,B_166),'#skF_2'(A_165,D_167))
      | ~ r2_hidden(D_167,B_166)
      | k1_xboole_0 = B_166
      | ~ r1_tarski(B_166,k3_relat_1(A_165))
      | ~ v2_wellord1(A_165)
      | ~ v1_relat_1(A_165) ) ),
    inference(resolution,[status(thm)],[c_351,c_14])).

tff(c_2258,plain,(
    ! [D_268,A_269] :
      ( ~ r2_hidden(D_268,'#skF_2'(A_269,D_268))
      | '#skF_2'(A_269,D_268) = k1_xboole_0
      | ~ r1_tarski('#skF_2'(A_269,D_268),k3_relat_1(A_269))
      | ~ v2_wellord1(A_269)
      | ~ v1_relat_1(A_269) ) ),
    inference(resolution,[status(thm)],[c_20,c_989])).

tff(c_2278,plain,
    ( '#skF_2'('#skF_4','#skF_5') = k1_xboole_0
    | ~ r1_tarski('#skF_2'('#skF_4','#skF_5'),k3_relat_1('#skF_4'))
    | ~ v2_wellord1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_251,c_2258])).

tff(c_2293,plain,
    ( '#skF_2'('#skF_4','#skF_5') = k1_xboole_0
    | ~ r1_tarski('#skF_2'('#skF_4','#skF_5'),k3_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_2278])).

tff(c_2296,plain,(
    ~ r1_tarski('#skF_2'('#skF_4','#skF_5'),k3_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2293])).

tff(c_2305,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_621,c_2296])).

tff(c_2318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2305])).

tff(c_2319,plain,(
    '#skF_2'('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2293])).

tff(c_30,plain,(
    r2_hidden('#skF_6',k3_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_28,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_248,plain,
    ( r2_hidden('#skF_6','#skF_2'('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_6',k3_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_223,c_28])).

tff(c_264,plain,(
    r2_hidden('#skF_6','#skF_2'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_248])).

tff(c_26,plain,(
    ! [B_30,A_29] :
      ( ~ v1_xboole_0(B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_276,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_264,c_26])).

tff(c_2325,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2319,c_276])).

tff(c_2329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_2325])).

%------------------------------------------------------------------------------
