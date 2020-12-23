%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:38 EST 2020

% Result     : Theorem 9.84s
% Output     : CNFRefutation 9.84s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 258 expanded)
%              Number of leaves         :   27 (  99 expanded)
%              Depth                    :   16
%              Number of atoms          :  233 ( 790 expanded)
%              Number of equality atoms :   10 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k2_xboole_0 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_101,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(c_40,plain,
    ( ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_15354,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_14,plain,(
    ! [A_14,B_16] :
      ( k10_relat_1(A_14,k1_relat_1(B_16)) = k1_relat_1(k5_relat_1(A_14,B_16))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_44,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_2'))
    | r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_64,plain,(
    r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_94,plain,(
    k2_xboole_0('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) = k1_relat_1(k5_relat_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_64,c_10])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2651,plain,(
    ! [A_201,C_202,B_203] :
      ( r2_hidden(A_201,k1_relat_1(C_202))
      | ~ r2_hidden(A_201,k1_relat_1(k5_relat_1(C_202,B_203)))
      | ~ v1_funct_1(C_202)
      | ~ v1_relat_1(C_202)
      | ~ v1_funct_1(B_203)
      | ~ v1_relat_1(B_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5670,plain,(
    ! [C_324,B_325,B_326] :
      ( r2_hidden('#skF_1'(k1_relat_1(k5_relat_1(C_324,B_325)),B_326),k1_relat_1(C_324))
      | ~ v1_funct_1(C_324)
      | ~ v1_relat_1(C_324)
      | ~ v1_funct_1(B_325)
      | ~ v1_relat_1(B_325)
      | r1_tarski(k1_relat_1(k5_relat_1(C_324,B_325)),B_326) ) ),
    inference(resolution,[status(thm)],[c_6,c_2651])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5683,plain,(
    ! [C_324,B_325] :
      ( ~ v1_funct_1(C_324)
      | ~ v1_relat_1(C_324)
      | ~ v1_funct_1(B_325)
      | ~ v1_relat_1(B_325)
      | r1_tarski(k1_relat_1(k5_relat_1(C_324,B_325)),k1_relat_1(C_324)) ) ),
    inference(resolution,[status(thm)],[c_5670,c_4])).

tff(c_293,plain,(
    ! [A_64,B_65] :
      ( k10_relat_1(A_64,k1_relat_1(B_65)) = k1_relat_1(k5_relat_1(A_64,B_65))
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k9_relat_1(B_18,k10_relat_1(B_18,A_17)),A_17)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3847,plain,(
    ! [A_257,B_258] :
      ( r1_tarski(k9_relat_1(A_257,k1_relat_1(k5_relat_1(A_257,B_258))),k1_relat_1(B_258))
      | ~ v1_funct_1(A_257)
      | ~ v1_relat_1(A_257)
      | ~ v1_relat_1(B_258)
      | ~ v1_relat_1(A_257) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_16])).

tff(c_18,plain,(
    ! [A_19,C_21,B_20] :
      ( r1_tarski(A_19,k10_relat_1(C_21,B_20))
      | ~ r1_tarski(k9_relat_1(C_21,A_19),B_20)
      | ~ r1_tarski(A_19,k1_relat_1(C_21))
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10474,plain,(
    ! [A_478,B_479] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_478,B_479)),k10_relat_1(A_478,k1_relat_1(B_479)))
      | ~ r1_tarski(k1_relat_1(k5_relat_1(A_478,B_479)),k1_relat_1(A_478))
      | ~ v1_funct_1(A_478)
      | ~ v1_relat_1(B_479)
      | ~ v1_relat_1(A_478) ) ),
    inference(resolution,[status(thm)],[c_3847,c_18])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_208,plain,(
    ! [C_8] :
      ( r1_tarski('#skF_5',C_8)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_2','#skF_3')),C_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_8])).

tff(c_10514,plain,
    ( r1_tarski('#skF_5',k10_relat_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_2','#skF_3')),k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10474,c_208])).

tff(c_10550,plain,
    ( r1_tarski('#skF_5',k10_relat_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_2','#skF_3')),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_30,c_10514])).

tff(c_10553,plain,(
    ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_2','#skF_3')),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_10550])).

tff(c_10556,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5683,c_10553])).

tff(c_10563,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_32,c_30,c_10556])).

tff(c_10564,plain,(
    r1_tarski('#skF_5',k10_relat_1('#skF_2',k1_relat_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_10550])).

tff(c_10599,plain,(
    k2_xboole_0('#skF_5',k10_relat_1('#skF_2',k1_relat_1('#skF_3'))) = k10_relat_1('#skF_2',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_10564,c_10])).

tff(c_11217,plain,
    ( k2_xboole_0('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) = k10_relat_1('#skF_2',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_10599])).

tff(c_11236,plain,(
    k10_relat_1('#skF_2',k1_relat_1('#skF_3')) = k1_relat_1(k5_relat_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_94,c_11217])).

tff(c_11756,plain,
    ( r1_tarski(k9_relat_1('#skF_2',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))),k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11236,c_16])).

tff(c_11774,plain,(
    r1_tarski(k9_relat_1('#skF_2',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_11756])).

tff(c_361,plain,(
    ! [C_71,A_72,B_73] :
      ( r1_tarski(k9_relat_1(C_71,A_72),k9_relat_1(C_71,B_73))
      | ~ r1_tarski(A_72,B_73)
      | ~ v1_relat_1(C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3225,plain,(
    ! [C_241,A_242,B_243] :
      ( k2_xboole_0(k9_relat_1(C_241,A_242),k9_relat_1(C_241,B_243)) = k9_relat_1(C_241,B_243)
      | ~ r1_tarski(A_242,B_243)
      | ~ v1_relat_1(C_241) ) ),
    inference(resolution,[status(thm)],[c_361,c_10])).

tff(c_3272,plain,(
    ! [C_241,A_242,C_8,B_243] :
      ( r1_tarski(k9_relat_1(C_241,A_242),C_8)
      | ~ r1_tarski(k9_relat_1(C_241,B_243),C_8)
      | ~ r1_tarski(A_242,B_243)
      | ~ v1_relat_1(C_241) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3225,c_8])).

tff(c_11781,plain,(
    ! [A_242] :
      ( r1_tarski(k9_relat_1('#skF_2',A_242),k1_relat_1('#skF_3'))
      | ~ r1_tarski(A_242,k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_11774,c_3272])).

tff(c_14589,plain,(
    ! [A_542] :
      ( r1_tarski(k9_relat_1('#skF_2',A_542),k1_relat_1('#skF_3'))
      | ~ r1_tarski(A_542,k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_11781])).

tff(c_48,plain,(
    ! [A_37,B_38] :
      ( ~ r2_hidden('#skF_1'(A_37,B_38),B_38)
      | r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_53,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_48])).

tff(c_151,plain,(
    ! [C_48,B_49,A_50] :
      ( r2_hidden(C_48,B_49)
      | ~ r2_hidden(C_48,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_284,plain,(
    ! [A_61,B_62,B_63] :
      ( r2_hidden('#skF_1'(A_61,B_62),B_63)
      | ~ r1_tarski(A_61,B_63)
      | r1_tarski(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_6,c_151])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_971,plain,(
    ! [A_111,B_112,B_113,B_114] :
      ( r2_hidden('#skF_1'(A_111,B_112),B_113)
      | ~ r1_tarski(B_114,B_113)
      | ~ r1_tarski(A_111,B_114)
      | r1_tarski(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_284,c_2])).

tff(c_1093,plain,(
    ! [A_122,B_123] :
      ( r2_hidden('#skF_1'(A_122,B_123),k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
      | ~ r1_tarski(A_122,'#skF_5')
      | r1_tarski(A_122,B_123) ) ),
    inference(resolution,[status(thm)],[c_64,c_971])).

tff(c_24,plain,(
    ! [A_22,C_25,B_23] :
      ( r2_hidden(A_22,k1_relat_1(C_25))
      | ~ r2_hidden(A_22,k1_relat_1(k5_relat_1(C_25,B_23)))
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1096,plain,(
    ! [A_122,B_123] :
      ( r2_hidden('#skF_1'(A_122,B_123),k1_relat_1('#skF_2'))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_122,'#skF_5')
      | r1_tarski(A_122,B_123) ) ),
    inference(resolution,[status(thm)],[c_1093,c_24])).

tff(c_1788,plain,(
    ! [A_156,B_157] :
      ( r2_hidden('#skF_1'(A_156,B_157),k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_156,'#skF_5')
      | r1_tarski(A_156,B_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_32,c_30,c_1096])).

tff(c_1802,plain,(
    ! [A_161] :
      ( ~ r1_tarski(A_161,'#skF_5')
      | r1_tarski(A_161,k1_relat_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1788,c_4])).

tff(c_38,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_367,plain,(
    ~ r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_1840,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_1802,c_367])).

tff(c_1870,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_1840])).

tff(c_1872,plain,(
    r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_34,plain,
    ( ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1902,plain,
    ( ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1872,c_34])).

tff(c_1903,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1902])).

tff(c_14613,plain,(
    ~ r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_14589,c_1903])).

tff(c_14634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_14613])).

tff(c_14635,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1902])).

tff(c_14636,plain,(
    r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1902])).

tff(c_1871,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3'))
    | r1_tarski('#skF_4',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_14794,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14636,c_1871])).

tff(c_36,plain,
    ( r1_tarski(k9_relat_1('#skF_2','#skF_4'),k1_relat_1('#skF_3'))
    | ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_14685,plain,(
    r1_tarski(k9_relat_1('#skF_2','#skF_4'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1872,c_14636,c_36])).

tff(c_15242,plain,(
    ! [A_576,C_577,B_578] :
      ( r1_tarski(A_576,k10_relat_1(C_577,B_578))
      | ~ r1_tarski(k9_relat_1(C_577,A_576),B_578)
      | ~ r1_tarski(A_576,k1_relat_1(C_577))
      | ~ v1_funct_1(C_577)
      | ~ v1_relat_1(C_577) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_15263,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14685,c_15242])).

tff(c_15313,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_2',k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_14794,c_15263])).

tff(c_15330,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_15313])).

tff(c_15333,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_15330])).

tff(c_15335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14635,c_15333])).

tff(c_15336,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_15337,plain,(
    ~ r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,
    ( r1_tarski(k9_relat_1('#skF_2','#skF_4'),k1_relat_1('#skF_3'))
    | r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_15480,plain,(
    r1_tarski(k9_relat_1('#skF_2','#skF_4'),k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_15337,c_42])).

tff(c_16440,plain,(
    ! [A_651,C_652,B_653] :
      ( r1_tarski(A_651,k10_relat_1(C_652,B_653))
      | ~ r1_tarski(k9_relat_1(C_652,A_651),B_653)
      | ~ r1_tarski(A_651,k1_relat_1(C_652))
      | ~ v1_funct_1(C_652)
      | ~ v1_relat_1(C_652) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16469,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_15480,c_16440])).

tff(c_16501,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_2',k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_15336,c_16469])).

tff(c_16510,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_16501])).

tff(c_16513,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_16510])).

tff(c_16515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15354,c_16513])).

tff(c_16516,plain,(
    r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_16542,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16516,c_15337])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:48:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.84/3.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.84/3.77  
% 9.84/3.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.84/3.77  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k2_xboole_0 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 9.84/3.77  
% 9.84/3.77  %Foreground sorts:
% 9.84/3.77  
% 9.84/3.77  
% 9.84/3.77  %Background operators:
% 9.84/3.77  
% 9.84/3.77  
% 9.84/3.77  %Foreground operators:
% 9.84/3.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.84/3.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.84/3.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.84/3.77  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.84/3.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.84/3.77  tff('#skF_5', type, '#skF_5': $i).
% 9.84/3.77  tff('#skF_2', type, '#skF_2': $i).
% 9.84/3.77  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.84/3.77  tff('#skF_3', type, '#skF_3': $i).
% 9.84/3.77  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.84/3.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.84/3.77  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.84/3.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.84/3.77  tff('#skF_4', type, '#skF_4': $i).
% 9.84/3.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.84/3.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.84/3.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.84/3.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.84/3.77  
% 9.84/3.79  tff(f_101, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 9.84/3.79  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 9.84/3.79  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.84/3.79  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.84/3.79  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 9.84/3.79  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 9.84/3.79  tff(f_69, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 9.84/3.79  tff(f_36, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 9.84/3.79  tff(f_46, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 9.84/3.79  tff(c_40, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.84/3.79  tff(c_15354, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_40])).
% 9.84/3.79  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.84/3.79  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.84/3.79  tff(c_14, plain, (![A_14, B_16]: (k10_relat_1(A_14, k1_relat_1(B_16))=k1_relat_1(k5_relat_1(A_14, B_16)) | ~v1_relat_1(B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.84/3.79  tff(c_30, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.84/3.79  tff(c_44, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2')) | r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.84/3.79  tff(c_64, plain, (r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_44])).
% 9.84/3.79  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.84/3.79  tff(c_94, plain, (k2_xboole_0('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))=k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_10])).
% 9.84/3.79  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.84/3.79  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.84/3.79  tff(c_2651, plain, (![A_201, C_202, B_203]: (r2_hidden(A_201, k1_relat_1(C_202)) | ~r2_hidden(A_201, k1_relat_1(k5_relat_1(C_202, B_203))) | ~v1_funct_1(C_202) | ~v1_relat_1(C_202) | ~v1_funct_1(B_203) | ~v1_relat_1(B_203))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.84/3.79  tff(c_5670, plain, (![C_324, B_325, B_326]: (r2_hidden('#skF_1'(k1_relat_1(k5_relat_1(C_324, B_325)), B_326), k1_relat_1(C_324)) | ~v1_funct_1(C_324) | ~v1_relat_1(C_324) | ~v1_funct_1(B_325) | ~v1_relat_1(B_325) | r1_tarski(k1_relat_1(k5_relat_1(C_324, B_325)), B_326))), inference(resolution, [status(thm)], [c_6, c_2651])).
% 9.84/3.79  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.84/3.79  tff(c_5683, plain, (![C_324, B_325]: (~v1_funct_1(C_324) | ~v1_relat_1(C_324) | ~v1_funct_1(B_325) | ~v1_relat_1(B_325) | r1_tarski(k1_relat_1(k5_relat_1(C_324, B_325)), k1_relat_1(C_324)))), inference(resolution, [status(thm)], [c_5670, c_4])).
% 9.84/3.79  tff(c_293, plain, (![A_64, B_65]: (k10_relat_1(A_64, k1_relat_1(B_65))=k1_relat_1(k5_relat_1(A_64, B_65)) | ~v1_relat_1(B_65) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.84/3.79  tff(c_16, plain, (![B_18, A_17]: (r1_tarski(k9_relat_1(B_18, k10_relat_1(B_18, A_17)), A_17) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.84/3.79  tff(c_3847, plain, (![A_257, B_258]: (r1_tarski(k9_relat_1(A_257, k1_relat_1(k5_relat_1(A_257, B_258))), k1_relat_1(B_258)) | ~v1_funct_1(A_257) | ~v1_relat_1(A_257) | ~v1_relat_1(B_258) | ~v1_relat_1(A_257))), inference(superposition, [status(thm), theory('equality')], [c_293, c_16])).
% 9.84/3.79  tff(c_18, plain, (![A_19, C_21, B_20]: (r1_tarski(A_19, k10_relat_1(C_21, B_20)) | ~r1_tarski(k9_relat_1(C_21, A_19), B_20) | ~r1_tarski(A_19, k1_relat_1(C_21)) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.84/3.79  tff(c_10474, plain, (![A_478, B_479]: (r1_tarski(k1_relat_1(k5_relat_1(A_478, B_479)), k10_relat_1(A_478, k1_relat_1(B_479))) | ~r1_tarski(k1_relat_1(k5_relat_1(A_478, B_479)), k1_relat_1(A_478)) | ~v1_funct_1(A_478) | ~v1_relat_1(B_479) | ~v1_relat_1(A_478))), inference(resolution, [status(thm)], [c_3847, c_18])).
% 9.84/3.79  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(k2_xboole_0(A_6, B_7), C_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.84/3.79  tff(c_208, plain, (![C_8]: (r1_tarski('#skF_5', C_8) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_2', '#skF_3')), C_8))), inference(superposition, [status(thm), theory('equality')], [c_94, c_8])).
% 9.84/3.79  tff(c_10514, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_2', k1_relat_1('#skF_3'))) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_2', '#skF_3')), k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10474, c_208])).
% 9.84/3.79  tff(c_10550, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_2', k1_relat_1('#skF_3'))) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_2', '#skF_3')), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_30, c_10514])).
% 9.84/3.79  tff(c_10553, plain, (~r1_tarski(k1_relat_1(k5_relat_1('#skF_2', '#skF_3')), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_10550])).
% 9.84/3.79  tff(c_10556, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5683, c_10553])).
% 9.84/3.79  tff(c_10563, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_32, c_30, c_10556])).
% 9.84/3.79  tff(c_10564, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_2', k1_relat_1('#skF_3')))), inference(splitRight, [status(thm)], [c_10550])).
% 9.84/3.79  tff(c_10599, plain, (k2_xboole_0('#skF_5', k10_relat_1('#skF_2', k1_relat_1('#skF_3')))=k10_relat_1('#skF_2', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_10564, c_10])).
% 9.84/3.79  tff(c_11217, plain, (k2_xboole_0('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))=k10_relat_1('#skF_2', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14, c_10599])).
% 9.84/3.79  tff(c_11236, plain, (k10_relat_1('#skF_2', k1_relat_1('#skF_3'))=k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_94, c_11217])).
% 9.84/3.79  tff(c_11756, plain, (r1_tarski(k9_relat_1('#skF_2', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))), k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11236, c_16])).
% 9.84/3.79  tff(c_11774, plain, (r1_tarski(k9_relat_1('#skF_2', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_11756])).
% 9.84/3.79  tff(c_361, plain, (![C_71, A_72, B_73]: (r1_tarski(k9_relat_1(C_71, A_72), k9_relat_1(C_71, B_73)) | ~r1_tarski(A_72, B_73) | ~v1_relat_1(C_71))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.84/3.79  tff(c_3225, plain, (![C_241, A_242, B_243]: (k2_xboole_0(k9_relat_1(C_241, A_242), k9_relat_1(C_241, B_243))=k9_relat_1(C_241, B_243) | ~r1_tarski(A_242, B_243) | ~v1_relat_1(C_241))), inference(resolution, [status(thm)], [c_361, c_10])).
% 9.84/3.79  tff(c_3272, plain, (![C_241, A_242, C_8, B_243]: (r1_tarski(k9_relat_1(C_241, A_242), C_8) | ~r1_tarski(k9_relat_1(C_241, B_243), C_8) | ~r1_tarski(A_242, B_243) | ~v1_relat_1(C_241))), inference(superposition, [status(thm), theory('equality')], [c_3225, c_8])).
% 9.84/3.79  tff(c_11781, plain, (![A_242]: (r1_tarski(k9_relat_1('#skF_2', A_242), k1_relat_1('#skF_3')) | ~r1_tarski(A_242, k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_11774, c_3272])).
% 9.84/3.79  tff(c_14589, plain, (![A_542]: (r1_tarski(k9_relat_1('#skF_2', A_542), k1_relat_1('#skF_3')) | ~r1_tarski(A_542, k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_11781])).
% 9.84/3.79  tff(c_48, plain, (![A_37, B_38]: (~r2_hidden('#skF_1'(A_37, B_38), B_38) | r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.84/3.79  tff(c_53, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_48])).
% 9.84/3.79  tff(c_151, plain, (![C_48, B_49, A_50]: (r2_hidden(C_48, B_49) | ~r2_hidden(C_48, A_50) | ~r1_tarski(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.84/3.79  tff(c_284, plain, (![A_61, B_62, B_63]: (r2_hidden('#skF_1'(A_61, B_62), B_63) | ~r1_tarski(A_61, B_63) | r1_tarski(A_61, B_62))), inference(resolution, [status(thm)], [c_6, c_151])).
% 9.84/3.79  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.84/3.79  tff(c_971, plain, (![A_111, B_112, B_113, B_114]: (r2_hidden('#skF_1'(A_111, B_112), B_113) | ~r1_tarski(B_114, B_113) | ~r1_tarski(A_111, B_114) | r1_tarski(A_111, B_112))), inference(resolution, [status(thm)], [c_284, c_2])).
% 9.84/3.79  tff(c_1093, plain, (![A_122, B_123]: (r2_hidden('#skF_1'(A_122, B_123), k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~r1_tarski(A_122, '#skF_5') | r1_tarski(A_122, B_123))), inference(resolution, [status(thm)], [c_64, c_971])).
% 9.84/3.79  tff(c_24, plain, (![A_22, C_25, B_23]: (r2_hidden(A_22, k1_relat_1(C_25)) | ~r2_hidden(A_22, k1_relat_1(k5_relat_1(C_25, B_23))) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.84/3.79  tff(c_1096, plain, (![A_122, B_123]: (r2_hidden('#skF_1'(A_122, B_123), k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_122, '#skF_5') | r1_tarski(A_122, B_123))), inference(resolution, [status(thm)], [c_1093, c_24])).
% 9.84/3.79  tff(c_1788, plain, (![A_156, B_157]: (r2_hidden('#skF_1'(A_156, B_157), k1_relat_1('#skF_2')) | ~r1_tarski(A_156, '#skF_5') | r1_tarski(A_156, B_157))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_32, c_30, c_1096])).
% 9.84/3.79  tff(c_1802, plain, (![A_161]: (~r1_tarski(A_161, '#skF_5') | r1_tarski(A_161, k1_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_1788, c_4])).
% 9.84/3.79  tff(c_38, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.84/3.79  tff(c_367, plain, (~r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_38])).
% 9.84/3.79  tff(c_1840, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_1802, c_367])).
% 9.84/3.79  tff(c_1870, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_1840])).
% 9.84/3.79  tff(c_1872, plain, (r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_38])).
% 9.84/3.79  tff(c_34, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.84/3.79  tff(c_1902, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1872, c_34])).
% 9.84/3.79  tff(c_1903, plain, (~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1902])).
% 9.84/3.79  tff(c_14613, plain, (~r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_14589, c_1903])).
% 9.84/3.79  tff(c_14634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_14613])).
% 9.84/3.79  tff(c_14635, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_1902])).
% 9.84/3.79  tff(c_14636, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1902])).
% 9.84/3.79  tff(c_1871, plain, (~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3')) | r1_tarski('#skF_4', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_38])).
% 9.84/3.79  tff(c_14794, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14636, c_1871])).
% 9.84/3.79  tff(c_36, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_4'), k1_relat_1('#skF_3')) | ~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.84/3.79  tff(c_14685, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_4'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1872, c_14636, c_36])).
% 9.84/3.79  tff(c_15242, plain, (![A_576, C_577, B_578]: (r1_tarski(A_576, k10_relat_1(C_577, B_578)) | ~r1_tarski(k9_relat_1(C_577, A_576), B_578) | ~r1_tarski(A_576, k1_relat_1(C_577)) | ~v1_funct_1(C_577) | ~v1_relat_1(C_577))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.84/3.79  tff(c_15263, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_2', k1_relat_1('#skF_3'))) | ~r1_tarski('#skF_4', k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_14685, c_15242])).
% 9.84/3.79  tff(c_15313, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_2', k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_14794, c_15263])).
% 9.84/3.79  tff(c_15330, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14, c_15313])).
% 9.84/3.79  tff(c_15333, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_15330])).
% 9.84/3.79  tff(c_15335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14635, c_15333])).
% 9.84/3.79  tff(c_15336, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_44])).
% 9.84/3.79  tff(c_15337, plain, (~r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_44])).
% 9.84/3.79  tff(c_42, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_4'), k1_relat_1('#skF_3')) | r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.84/3.79  tff(c_15480, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_4'), k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_15337, c_42])).
% 9.84/3.79  tff(c_16440, plain, (![A_651, C_652, B_653]: (r1_tarski(A_651, k10_relat_1(C_652, B_653)) | ~r1_tarski(k9_relat_1(C_652, A_651), B_653) | ~r1_tarski(A_651, k1_relat_1(C_652)) | ~v1_funct_1(C_652) | ~v1_relat_1(C_652))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.84/3.79  tff(c_16469, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_2', k1_relat_1('#skF_3'))) | ~r1_tarski('#skF_4', k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_15480, c_16440])).
% 9.84/3.79  tff(c_16501, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_2', k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_15336, c_16469])).
% 9.84/3.79  tff(c_16510, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14, c_16501])).
% 9.84/3.79  tff(c_16513, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_16510])).
% 9.84/3.79  tff(c_16515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15354, c_16513])).
% 9.84/3.79  tff(c_16516, plain, (r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_40])).
% 9.84/3.79  tff(c_16542, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16516, c_15337])).
% 9.84/3.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.84/3.79  
% 9.84/3.79  Inference rules
% 9.84/3.79  ----------------------
% 9.84/3.79  #Ref     : 0
% 9.84/3.79  #Sup     : 4140
% 9.84/3.79  #Fact    : 0
% 9.84/3.79  #Define  : 0
% 9.84/3.79  #Split   : 6
% 9.84/3.79  #Chain   : 0
% 9.84/3.79  #Close   : 0
% 9.84/3.79  
% 9.84/3.79  Ordering : KBO
% 9.84/3.79  
% 9.84/3.79  Simplification rules
% 9.84/3.79  ----------------------
% 9.84/3.79  #Subsume      : 780
% 9.84/3.79  #Demod        : 1270
% 9.84/3.79  #Tautology    : 1102
% 9.84/3.79  #SimpNegUnit  : 5
% 9.84/3.79  #BackRed      : 4
% 9.84/3.79  
% 9.84/3.79  #Partial instantiations: 0
% 9.84/3.79  #Strategies tried      : 1
% 9.84/3.79  
% 9.84/3.79  Timing (in seconds)
% 9.84/3.79  ----------------------
% 9.84/3.79  Preprocessing        : 0.32
% 9.84/3.79  Parsing              : 0.17
% 9.84/3.79  CNF conversion       : 0.02
% 9.84/3.79  Main loop            : 2.68
% 9.84/3.79  Inferencing          : 0.62
% 9.84/3.79  Reduction            : 0.88
% 9.84/3.79  Demodulation         : 0.70
% 9.84/3.79  BG Simplification    : 0.08
% 9.84/3.79  Subsumption          : 0.94
% 9.84/3.79  Abstraction          : 0.09
% 9.84/3.79  MUC search           : 0.00
% 9.84/3.79  Cooper               : 0.00
% 9.84/3.79  Total                : 3.04
% 9.84/3.79  Index Insertion      : 0.00
% 9.84/3.79  Index Deletion       : 0.00
% 9.84/3.79  Index Matching       : 0.00
% 9.84/3.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
