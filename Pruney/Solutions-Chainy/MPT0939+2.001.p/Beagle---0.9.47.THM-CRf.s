%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:30 EST 2020

% Result     : Theorem 4.69s
% Output     : CNFRefutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 130 expanded)
%              Number of leaves         :   29 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  165 ( 330 expanded)
%              Number of equality atoms :    5 (  31 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v6_relat_2 > v3_ordinal1 > v2_ordinal1 > v1_relat_1 > v1_ordinal1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_2 > #skF_1 > #skF_6 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(v6_relat_2,type,(
    v6_relat_2: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => v6_relat_2(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_wellord2)).

tff(f_97,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v6_relat_2(A)
      <=> ! [B,C] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r2_hidden(C,k3_relat_1(A))
              & B != C
              & ~ r2_hidden(k4_tarski(B,C),A)
              & ~ r2_hidden(k4_tarski(C,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_31,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_61,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(c_54,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_50,plain,(
    ! [A_28] : v1_relat_1(k1_wellord2(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_44,plain,(
    ! [A_20] :
      ( k3_relat_1(k1_wellord2(A_20)) = A_20
      | ~ v1_relat_1(k1_wellord2(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_60,plain,(
    ! [A_20] : k3_relat_1(k1_wellord2(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44])).

tff(c_114,plain,(
    ! [A_41] :
      ( r2_hidden('#skF_3'(A_41),k3_relat_1(A_41))
      | v6_relat_2(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_123,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_3'(k1_wellord2(A_20)),A_20)
      | v6_relat_2(k1_wellord2(A_20))
      | ~ v1_relat_1(k1_wellord2(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_114])).

tff(c_137,plain,(
    ! [A_43] :
      ( r2_hidden('#skF_3'(k1_wellord2(A_43)),A_43)
      | v6_relat_2(k1_wellord2(A_43)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_123])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( v3_ordinal1(A_8)
      | ~ r2_hidden(A_8,B_9)
      | ~ v3_ordinal1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_156,plain,(
    ! [A_47] :
      ( v3_ordinal1('#skF_3'(k1_wellord2(A_47)))
      | ~ v3_ordinal1(A_47)
      | v6_relat_2(k1_wellord2(A_47)) ) ),
    inference(resolution,[status(thm)],[c_137,c_16])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_ordinal1(A_1)
      | ~ v3_ordinal1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_163,plain,(
    ! [A_47] :
      ( v1_ordinal1('#skF_3'(k1_wellord2(A_47)))
      | ~ v3_ordinal1(A_47)
      | v6_relat_2(k1_wellord2(A_47)) ) ),
    inference(resolution,[status(thm)],[c_156,c_4])).

tff(c_145,plain,(
    ! [A_43] :
      ( v3_ordinal1('#skF_3'(k1_wellord2(A_43)))
      | ~ v3_ordinal1(A_43)
      | v6_relat_2(k1_wellord2(A_43)) ) ),
    inference(resolution,[status(thm)],[c_137,c_16])).

tff(c_100,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_2'(A_40),k3_relat_1(A_40))
      | v6_relat_2(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_109,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_2'(k1_wellord2(A_20)),A_20)
      | v6_relat_2(k1_wellord2(A_20))
      | ~ v1_relat_1(k1_wellord2(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_100])).

tff(c_128,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_2'(k1_wellord2(A_42)),A_42)
      | v6_relat_2(k1_wellord2(A_42)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_109])).

tff(c_136,plain,(
    ! [A_42] :
      ( v3_ordinal1('#skF_2'(k1_wellord2(A_42)))
      | ~ v3_ordinal1(A_42)
      | v6_relat_2(k1_wellord2(A_42)) ) ),
    inference(resolution,[status(thm)],[c_128,c_16])).

tff(c_127,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_3'(k1_wellord2(A_20)),A_20)
      | v6_relat_2(k1_wellord2(A_20)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_123])).

tff(c_113,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_2'(k1_wellord2(A_20)),A_20)
      | v6_relat_2(k1_wellord2(A_20)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_109])).

tff(c_179,plain,(
    ! [B_54,A_55] :
      ( r2_hidden(B_54,A_55)
      | r1_ordinal1(A_55,B_54)
      | ~ v3_ordinal1(B_54)
      | ~ v3_ordinal1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [B_5,A_2] :
      ( r1_tarski(B_5,A_2)
      | ~ r2_hidden(B_5,A_2)
      | ~ v1_ordinal1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_186,plain,(
    ! [B_54,A_55] :
      ( r1_tarski(B_54,A_55)
      | ~ v1_ordinal1(A_55)
      | r1_ordinal1(A_55,B_54)
      | ~ v3_ordinal1(B_54)
      | ~ v3_ordinal1(A_55) ) ),
    inference(resolution,[status(thm)],[c_179,c_6])).

tff(c_46,plain,(
    ! [C_26,D_27,A_20] :
      ( r2_hidden(k4_tarski(C_26,D_27),k1_wellord2(A_20))
      | ~ r1_tarski(C_26,D_27)
      | ~ r2_hidden(D_27,A_20)
      | ~ r2_hidden(C_26,A_20)
      | ~ v1_relat_1(k1_wellord2(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_346,plain,(
    ! [C_75,D_76,A_77] :
      ( r2_hidden(k4_tarski(C_75,D_76),k1_wellord2(A_77))
      | ~ r1_tarski(C_75,D_76)
      | ~ r2_hidden(D_76,A_77)
      | ~ r2_hidden(C_75,A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46])).

tff(c_24,plain,(
    ! [A_13] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(A_13),'#skF_3'(A_13)),A_13)
      | v6_relat_2(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_350,plain,(
    ! [A_77] :
      ( v6_relat_2(k1_wellord2(A_77))
      | ~ v1_relat_1(k1_wellord2(A_77))
      | ~ r1_tarski('#skF_2'(k1_wellord2(A_77)),'#skF_3'(k1_wellord2(A_77)))
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_77)),A_77)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_77)),A_77) ) ),
    inference(resolution,[status(thm)],[c_346,c_24])).

tff(c_560,plain,(
    ! [A_102] :
      ( v6_relat_2(k1_wellord2(A_102))
      | ~ r1_tarski('#skF_2'(k1_wellord2(A_102)),'#skF_3'(k1_wellord2(A_102)))
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_102)),A_102)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_102)),A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_350])).

tff(c_1721,plain,(
    ! [A_230] :
      ( v6_relat_2(k1_wellord2(A_230))
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_230)),A_230)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_230)),A_230)
      | ~ v1_ordinal1('#skF_3'(k1_wellord2(A_230)))
      | r1_ordinal1('#skF_3'(k1_wellord2(A_230)),'#skF_2'(k1_wellord2(A_230)))
      | ~ v3_ordinal1('#skF_2'(k1_wellord2(A_230)))
      | ~ v3_ordinal1('#skF_3'(k1_wellord2(A_230))) ) ),
    inference(resolution,[status(thm)],[c_186,c_560])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ r1_ordinal1(A_6,B_7)
      | ~ v3_ordinal1(B_7)
      | ~ v3_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    ! [A_13] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_13),'#skF_2'(A_13)),A_13)
      | v6_relat_2(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_354,plain,(
    ! [A_77] :
      ( v6_relat_2(k1_wellord2(A_77))
      | ~ v1_relat_1(k1_wellord2(A_77))
      | ~ r1_tarski('#skF_3'(k1_wellord2(A_77)),'#skF_2'(k1_wellord2(A_77)))
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_77)),A_77)
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_77)),A_77) ) ),
    inference(resolution,[status(thm)],[c_346,c_22])).

tff(c_569,plain,(
    ! [A_103] :
      ( v6_relat_2(k1_wellord2(A_103))
      | ~ r1_tarski('#skF_3'(k1_wellord2(A_103)),'#skF_2'(k1_wellord2(A_103)))
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_103)),A_103)
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_103)),A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_354])).

tff(c_577,plain,(
    ! [A_103] :
      ( v6_relat_2(k1_wellord2(A_103))
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_103)),A_103)
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_103)),A_103)
      | ~ r1_ordinal1('#skF_3'(k1_wellord2(A_103)),'#skF_2'(k1_wellord2(A_103)))
      | ~ v3_ordinal1('#skF_2'(k1_wellord2(A_103)))
      | ~ v3_ordinal1('#skF_3'(k1_wellord2(A_103))) ) ),
    inference(resolution,[status(thm)],[c_14,c_569])).

tff(c_1726,plain,(
    ! [A_231] :
      ( v6_relat_2(k1_wellord2(A_231))
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_231)),A_231)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_231)),A_231)
      | ~ v1_ordinal1('#skF_3'(k1_wellord2(A_231)))
      | ~ v3_ordinal1('#skF_2'(k1_wellord2(A_231)))
      | ~ v3_ordinal1('#skF_3'(k1_wellord2(A_231))) ) ),
    inference(resolution,[status(thm)],[c_1721,c_577])).

tff(c_1736,plain,(
    ! [A_232] :
      ( ~ r2_hidden('#skF_3'(k1_wellord2(A_232)),A_232)
      | ~ v1_ordinal1('#skF_3'(k1_wellord2(A_232)))
      | ~ v3_ordinal1('#skF_2'(k1_wellord2(A_232)))
      | ~ v3_ordinal1('#skF_3'(k1_wellord2(A_232)))
      | v6_relat_2(k1_wellord2(A_232)) ) ),
    inference(resolution,[status(thm)],[c_113,c_1726])).

tff(c_1746,plain,(
    ! [A_233] :
      ( ~ v1_ordinal1('#skF_3'(k1_wellord2(A_233)))
      | ~ v3_ordinal1('#skF_2'(k1_wellord2(A_233)))
      | ~ v3_ordinal1('#skF_3'(k1_wellord2(A_233)))
      | v6_relat_2(k1_wellord2(A_233)) ) ),
    inference(resolution,[status(thm)],[c_127,c_1736])).

tff(c_1751,plain,(
    ! [A_234] :
      ( ~ v1_ordinal1('#skF_3'(k1_wellord2(A_234)))
      | ~ v3_ordinal1('#skF_3'(k1_wellord2(A_234)))
      | ~ v3_ordinal1(A_234)
      | v6_relat_2(k1_wellord2(A_234)) ) ),
    inference(resolution,[status(thm)],[c_136,c_1746])).

tff(c_1756,plain,(
    ! [A_235] :
      ( ~ v1_ordinal1('#skF_3'(k1_wellord2(A_235)))
      | ~ v3_ordinal1(A_235)
      | v6_relat_2(k1_wellord2(A_235)) ) ),
    inference(resolution,[status(thm)],[c_145,c_1751])).

tff(c_1761,plain,(
    ! [A_236] :
      ( ~ v3_ordinal1(A_236)
      | v6_relat_2(k1_wellord2(A_236)) ) ),
    inference(resolution,[status(thm)],[c_163,c_1756])).

tff(c_52,plain,(
    ~ v6_relat_2(k1_wellord2('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1782,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1761,c_52])).

tff(c_1793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1782])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:37:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.69/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.85  
% 4.83/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.85  %$ r2_hidden > r1_tarski > r1_ordinal1 > v6_relat_2 > v3_ordinal1 > v2_ordinal1 > v1_relat_1 > v1_ordinal1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_2 > #skF_1 > #skF_6 > #skF_3 > #skF_5 > #skF_4
% 4.83/1.85  
% 4.83/1.85  %Foreground sorts:
% 4.83/1.85  
% 4.83/1.85  
% 4.83/1.85  %Background operators:
% 4.83/1.85  
% 4.83/1.85  
% 4.83/1.85  %Foreground operators:
% 4.83/1.85  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.83/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.83/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.83/1.85  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 4.83/1.85  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.83/1.85  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.83/1.85  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 4.83/1.85  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 4.83/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.83/1.85  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 4.83/1.85  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 4.83/1.85  tff('#skF_6', type, '#skF_6': $i).
% 4.83/1.85  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 4.83/1.85  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 4.83/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.83/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.83/1.85  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.83/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.83/1.85  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.83/1.85  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.83/1.85  
% 4.83/1.87  tff(f_102, negated_conjecture, ~(![A]: (v3_ordinal1(A) => v6_relat_2(k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_wellord2)).
% 4.83/1.87  tff(f_97, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 4.83/1.87  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 4.83/1.87  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (v6_relat_2(A) <=> (![B, C]: ~((((r2_hidden(B, k3_relat_1(A)) & r2_hidden(C, k3_relat_1(A))) & ~(B = C)) & ~r2_hidden(k4_tarski(B, C), A)) & ~r2_hidden(k4_tarski(C, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l4_wellord1)).
% 4.83/1.87  tff(f_52, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 4.83/1.87  tff(f_31, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 4.83/1.87  tff(f_61, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 4.83/1.87  tff(f_38, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 4.83/1.87  tff(f_46, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 4.83/1.87  tff(c_54, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.83/1.87  tff(c_50, plain, (![A_28]: (v1_relat_1(k1_wellord2(A_28)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.83/1.87  tff(c_44, plain, (![A_20]: (k3_relat_1(k1_wellord2(A_20))=A_20 | ~v1_relat_1(k1_wellord2(A_20)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.83/1.87  tff(c_60, plain, (![A_20]: (k3_relat_1(k1_wellord2(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44])).
% 4.83/1.87  tff(c_114, plain, (![A_41]: (r2_hidden('#skF_3'(A_41), k3_relat_1(A_41)) | v6_relat_2(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.83/1.87  tff(c_123, plain, (![A_20]: (r2_hidden('#skF_3'(k1_wellord2(A_20)), A_20) | v6_relat_2(k1_wellord2(A_20)) | ~v1_relat_1(k1_wellord2(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_114])).
% 4.83/1.87  tff(c_137, plain, (![A_43]: (r2_hidden('#skF_3'(k1_wellord2(A_43)), A_43) | v6_relat_2(k1_wellord2(A_43)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_123])).
% 4.83/1.87  tff(c_16, plain, (![A_8, B_9]: (v3_ordinal1(A_8) | ~r2_hidden(A_8, B_9) | ~v3_ordinal1(B_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.83/1.87  tff(c_156, plain, (![A_47]: (v3_ordinal1('#skF_3'(k1_wellord2(A_47))) | ~v3_ordinal1(A_47) | v6_relat_2(k1_wellord2(A_47)))), inference(resolution, [status(thm)], [c_137, c_16])).
% 4.83/1.87  tff(c_4, plain, (![A_1]: (v1_ordinal1(A_1) | ~v3_ordinal1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.83/1.87  tff(c_163, plain, (![A_47]: (v1_ordinal1('#skF_3'(k1_wellord2(A_47))) | ~v3_ordinal1(A_47) | v6_relat_2(k1_wellord2(A_47)))), inference(resolution, [status(thm)], [c_156, c_4])).
% 4.83/1.87  tff(c_145, plain, (![A_43]: (v3_ordinal1('#skF_3'(k1_wellord2(A_43))) | ~v3_ordinal1(A_43) | v6_relat_2(k1_wellord2(A_43)))), inference(resolution, [status(thm)], [c_137, c_16])).
% 4.83/1.87  tff(c_100, plain, (![A_40]: (r2_hidden('#skF_2'(A_40), k3_relat_1(A_40)) | v6_relat_2(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.83/1.87  tff(c_109, plain, (![A_20]: (r2_hidden('#skF_2'(k1_wellord2(A_20)), A_20) | v6_relat_2(k1_wellord2(A_20)) | ~v1_relat_1(k1_wellord2(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_100])).
% 4.83/1.87  tff(c_128, plain, (![A_42]: (r2_hidden('#skF_2'(k1_wellord2(A_42)), A_42) | v6_relat_2(k1_wellord2(A_42)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_109])).
% 4.83/1.87  tff(c_136, plain, (![A_42]: (v3_ordinal1('#skF_2'(k1_wellord2(A_42))) | ~v3_ordinal1(A_42) | v6_relat_2(k1_wellord2(A_42)))), inference(resolution, [status(thm)], [c_128, c_16])).
% 4.83/1.87  tff(c_127, plain, (![A_20]: (r2_hidden('#skF_3'(k1_wellord2(A_20)), A_20) | v6_relat_2(k1_wellord2(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_123])).
% 4.83/1.87  tff(c_113, plain, (![A_20]: (r2_hidden('#skF_2'(k1_wellord2(A_20)), A_20) | v6_relat_2(k1_wellord2(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_109])).
% 4.83/1.87  tff(c_179, plain, (![B_54, A_55]: (r2_hidden(B_54, A_55) | r1_ordinal1(A_55, B_54) | ~v3_ordinal1(B_54) | ~v3_ordinal1(A_55))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.83/1.87  tff(c_6, plain, (![B_5, A_2]: (r1_tarski(B_5, A_2) | ~r2_hidden(B_5, A_2) | ~v1_ordinal1(A_2))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.83/1.87  tff(c_186, plain, (![B_54, A_55]: (r1_tarski(B_54, A_55) | ~v1_ordinal1(A_55) | r1_ordinal1(A_55, B_54) | ~v3_ordinal1(B_54) | ~v3_ordinal1(A_55))), inference(resolution, [status(thm)], [c_179, c_6])).
% 4.83/1.87  tff(c_46, plain, (![C_26, D_27, A_20]: (r2_hidden(k4_tarski(C_26, D_27), k1_wellord2(A_20)) | ~r1_tarski(C_26, D_27) | ~r2_hidden(D_27, A_20) | ~r2_hidden(C_26, A_20) | ~v1_relat_1(k1_wellord2(A_20)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.83/1.87  tff(c_346, plain, (![C_75, D_76, A_77]: (r2_hidden(k4_tarski(C_75, D_76), k1_wellord2(A_77)) | ~r1_tarski(C_75, D_76) | ~r2_hidden(D_76, A_77) | ~r2_hidden(C_75, A_77))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46])).
% 4.83/1.87  tff(c_24, plain, (![A_13]: (~r2_hidden(k4_tarski('#skF_2'(A_13), '#skF_3'(A_13)), A_13) | v6_relat_2(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.83/1.87  tff(c_350, plain, (![A_77]: (v6_relat_2(k1_wellord2(A_77)) | ~v1_relat_1(k1_wellord2(A_77)) | ~r1_tarski('#skF_2'(k1_wellord2(A_77)), '#skF_3'(k1_wellord2(A_77))) | ~r2_hidden('#skF_3'(k1_wellord2(A_77)), A_77) | ~r2_hidden('#skF_2'(k1_wellord2(A_77)), A_77))), inference(resolution, [status(thm)], [c_346, c_24])).
% 4.83/1.87  tff(c_560, plain, (![A_102]: (v6_relat_2(k1_wellord2(A_102)) | ~r1_tarski('#skF_2'(k1_wellord2(A_102)), '#skF_3'(k1_wellord2(A_102))) | ~r2_hidden('#skF_3'(k1_wellord2(A_102)), A_102) | ~r2_hidden('#skF_2'(k1_wellord2(A_102)), A_102))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_350])).
% 4.83/1.87  tff(c_1721, plain, (![A_230]: (v6_relat_2(k1_wellord2(A_230)) | ~r2_hidden('#skF_3'(k1_wellord2(A_230)), A_230) | ~r2_hidden('#skF_2'(k1_wellord2(A_230)), A_230) | ~v1_ordinal1('#skF_3'(k1_wellord2(A_230))) | r1_ordinal1('#skF_3'(k1_wellord2(A_230)), '#skF_2'(k1_wellord2(A_230))) | ~v3_ordinal1('#skF_2'(k1_wellord2(A_230))) | ~v3_ordinal1('#skF_3'(k1_wellord2(A_230))))), inference(resolution, [status(thm)], [c_186, c_560])).
% 4.83/1.87  tff(c_14, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~r1_ordinal1(A_6, B_7) | ~v3_ordinal1(B_7) | ~v3_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.83/1.87  tff(c_22, plain, (![A_13]: (~r2_hidden(k4_tarski('#skF_3'(A_13), '#skF_2'(A_13)), A_13) | v6_relat_2(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.83/1.87  tff(c_354, plain, (![A_77]: (v6_relat_2(k1_wellord2(A_77)) | ~v1_relat_1(k1_wellord2(A_77)) | ~r1_tarski('#skF_3'(k1_wellord2(A_77)), '#skF_2'(k1_wellord2(A_77))) | ~r2_hidden('#skF_2'(k1_wellord2(A_77)), A_77) | ~r2_hidden('#skF_3'(k1_wellord2(A_77)), A_77))), inference(resolution, [status(thm)], [c_346, c_22])).
% 4.83/1.87  tff(c_569, plain, (![A_103]: (v6_relat_2(k1_wellord2(A_103)) | ~r1_tarski('#skF_3'(k1_wellord2(A_103)), '#skF_2'(k1_wellord2(A_103))) | ~r2_hidden('#skF_2'(k1_wellord2(A_103)), A_103) | ~r2_hidden('#skF_3'(k1_wellord2(A_103)), A_103))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_354])).
% 4.83/1.87  tff(c_577, plain, (![A_103]: (v6_relat_2(k1_wellord2(A_103)) | ~r2_hidden('#skF_2'(k1_wellord2(A_103)), A_103) | ~r2_hidden('#skF_3'(k1_wellord2(A_103)), A_103) | ~r1_ordinal1('#skF_3'(k1_wellord2(A_103)), '#skF_2'(k1_wellord2(A_103))) | ~v3_ordinal1('#skF_2'(k1_wellord2(A_103))) | ~v3_ordinal1('#skF_3'(k1_wellord2(A_103))))), inference(resolution, [status(thm)], [c_14, c_569])).
% 4.83/1.87  tff(c_1726, plain, (![A_231]: (v6_relat_2(k1_wellord2(A_231)) | ~r2_hidden('#skF_3'(k1_wellord2(A_231)), A_231) | ~r2_hidden('#skF_2'(k1_wellord2(A_231)), A_231) | ~v1_ordinal1('#skF_3'(k1_wellord2(A_231))) | ~v3_ordinal1('#skF_2'(k1_wellord2(A_231))) | ~v3_ordinal1('#skF_3'(k1_wellord2(A_231))))), inference(resolution, [status(thm)], [c_1721, c_577])).
% 4.83/1.87  tff(c_1736, plain, (![A_232]: (~r2_hidden('#skF_3'(k1_wellord2(A_232)), A_232) | ~v1_ordinal1('#skF_3'(k1_wellord2(A_232))) | ~v3_ordinal1('#skF_2'(k1_wellord2(A_232))) | ~v3_ordinal1('#skF_3'(k1_wellord2(A_232))) | v6_relat_2(k1_wellord2(A_232)))), inference(resolution, [status(thm)], [c_113, c_1726])).
% 4.83/1.87  tff(c_1746, plain, (![A_233]: (~v1_ordinal1('#skF_3'(k1_wellord2(A_233))) | ~v3_ordinal1('#skF_2'(k1_wellord2(A_233))) | ~v3_ordinal1('#skF_3'(k1_wellord2(A_233))) | v6_relat_2(k1_wellord2(A_233)))), inference(resolution, [status(thm)], [c_127, c_1736])).
% 4.83/1.87  tff(c_1751, plain, (![A_234]: (~v1_ordinal1('#skF_3'(k1_wellord2(A_234))) | ~v3_ordinal1('#skF_3'(k1_wellord2(A_234))) | ~v3_ordinal1(A_234) | v6_relat_2(k1_wellord2(A_234)))), inference(resolution, [status(thm)], [c_136, c_1746])).
% 4.83/1.87  tff(c_1756, plain, (![A_235]: (~v1_ordinal1('#skF_3'(k1_wellord2(A_235))) | ~v3_ordinal1(A_235) | v6_relat_2(k1_wellord2(A_235)))), inference(resolution, [status(thm)], [c_145, c_1751])).
% 4.83/1.87  tff(c_1761, plain, (![A_236]: (~v3_ordinal1(A_236) | v6_relat_2(k1_wellord2(A_236)))), inference(resolution, [status(thm)], [c_163, c_1756])).
% 4.83/1.87  tff(c_52, plain, (~v6_relat_2(k1_wellord2('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.83/1.87  tff(c_1782, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_1761, c_52])).
% 4.83/1.87  tff(c_1793, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_1782])).
% 4.83/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.87  
% 4.83/1.87  Inference rules
% 4.83/1.87  ----------------------
% 4.83/1.87  #Ref     : 0
% 4.83/1.87  #Sup     : 367
% 4.83/1.87  #Fact    : 16
% 4.83/1.87  #Define  : 0
% 4.83/1.87  #Split   : 0
% 4.83/1.87  #Chain   : 0
% 4.83/1.87  #Close   : 0
% 4.83/1.87  
% 4.83/1.87  Ordering : KBO
% 4.83/1.87  
% 4.83/1.87  Simplification rules
% 4.83/1.87  ----------------------
% 4.83/1.87  #Subsume      : 47
% 4.83/1.87  #Demod        : 249
% 4.83/1.87  #Tautology    : 103
% 4.83/1.87  #SimpNegUnit  : 0
% 4.83/1.87  #BackRed      : 0
% 4.83/1.87  
% 4.83/1.87  #Partial instantiations: 0
% 4.83/1.87  #Strategies tried      : 1
% 4.83/1.87  
% 4.83/1.87  Timing (in seconds)
% 4.83/1.87  ----------------------
% 4.83/1.87  Preprocessing        : 0.32
% 4.83/1.87  Parsing              : 0.16
% 4.83/1.87  CNF conversion       : 0.02
% 4.83/1.87  Main loop            : 0.79
% 4.83/1.87  Inferencing          : 0.29
% 4.83/1.87  Reduction            : 0.19
% 4.83/1.87  Demodulation         : 0.13
% 4.83/1.87  BG Simplification    : 0.04
% 4.83/1.87  Subsumption          : 0.22
% 4.83/1.87  Abstraction          : 0.04
% 4.83/1.87  MUC search           : 0.00
% 4.83/1.87  Cooper               : 0.00
% 4.83/1.87  Total                : 1.14
% 4.83/1.87  Index Insertion      : 0.00
% 4.83/1.87  Index Deletion       : 0.00
% 4.83/1.87  Index Matching       : 0.00
% 4.83/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
