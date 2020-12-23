%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0746+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:48 EST 2020

% Result     : Theorem 4.32s
% Output     : CNFRefutation 4.32s
% Verified   : 
% Statistics : Number of formulae       :   53 (  79 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   86 ( 155 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v1_xboole_0 > #nlpp > k3_tarski > k1_ordinal1 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_72,axiom,(
    ! [A] :
      ( ! [B] :
          ( r2_hidden(B,A)
         => v3_ordinal1(B) )
     => v3_ordinal1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_ordinal1)).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ~ ( ! [B] :
              ( r2_hidden(B,A)
             => v3_ordinal1(B) )
          & ! [B] :
              ( v3_ordinal1(B)
             => ~ r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_ordinal1)).

tff(f_48,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( ~ v1_xboole_0(k1_ordinal1(A))
        & v3_ordinal1(k1_ordinal1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_ordinal1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_65,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,k1_ordinal1(B))
          <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(c_50,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_6'(A_42),A_42)
      | v3_ordinal1(k3_tarski(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_44,plain,(
    ! [B_35] :
      ( v3_ordinal1(B_35)
      | ~ r2_hidden(B_35,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_55,plain,
    ( v3_ordinal1('#skF_6'('#skF_7'))
    | v3_ordinal1(k3_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_50,c_44])).

tff(c_56,plain,(
    v3_ordinal1(k3_tarski('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_26,plain,(
    ! [A_25] :
      ( v3_ordinal1(k1_ordinal1(A_25))
      | ~ v3_ordinal1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_57,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_1'(A_43,B_44),A_43)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [B_44] :
      ( v3_ordinal1('#skF_1'('#skF_7',B_44))
      | r1_tarski('#skF_7',B_44) ) ),
    inference(resolution,[status(thm)],[c_57,c_44])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [C_54,A_55,D_56] :
      ( r2_hidden(C_54,k3_tarski(A_55))
      | ~ r2_hidden(D_56,A_55)
      | ~ r2_hidden(C_54,D_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_252,plain,(
    ! [C_83,A_84,B_85] :
      ( r2_hidden(C_83,k3_tarski(A_84))
      | ~ r2_hidden(C_83,'#skF_1'(A_84,B_85))
      | r1_tarski(A_84,B_85) ) ),
    inference(resolution,[status(thm)],[c_6,c_88])).

tff(c_1415,plain,(
    ! [A_185,B_186,B_187] :
      ( r2_hidden('#skF_1'('#skF_1'(A_185,B_186),B_187),k3_tarski(A_185))
      | r1_tarski(A_185,B_186)
      | r1_tarski('#skF_1'(A_185,B_186),B_187) ) ),
    inference(resolution,[status(thm)],[c_6,c_252])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1436,plain,(
    ! [A_188,B_189] :
      ( r1_tarski(A_188,B_189)
      | r1_tarski('#skF_1'(A_188,B_189),k3_tarski(A_188)) ) ),
    inference(resolution,[status(thm)],[c_1415,c_4])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( r1_ordinal1(A_26,B_27)
      | ~ r1_tarski(A_26,B_27)
      | ~ v3_ordinal1(B_27)
      | ~ v3_ordinal1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1446,plain,(
    ! [A_188,B_189] :
      ( r1_ordinal1('#skF_1'(A_188,B_189),k3_tarski(A_188))
      | ~ v3_ordinal1(k3_tarski(A_188))
      | ~ v3_ordinal1('#skF_1'(A_188,B_189))
      | r1_tarski(A_188,B_189) ) ),
    inference(resolution,[status(thm)],[c_1436,c_30])).

tff(c_139,plain,(
    ! [A_68,B_69] :
      ( r2_hidden(A_68,k1_ordinal1(B_69))
      | ~ r1_ordinal1(A_68,B_69)
      | ~ v3_ordinal1(B_69)
      | ~ v3_ordinal1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1787,plain,(
    ! [A_215,B_216] :
      ( r1_tarski(A_215,k1_ordinal1(B_216))
      | ~ r1_ordinal1('#skF_1'(A_215,k1_ordinal1(B_216)),B_216)
      | ~ v3_ordinal1(B_216)
      | ~ v3_ordinal1('#skF_1'(A_215,k1_ordinal1(B_216))) ) ),
    inference(resolution,[status(thm)],[c_139,c_4])).

tff(c_1793,plain,(
    ! [A_217] :
      ( ~ v3_ordinal1(k3_tarski(A_217))
      | ~ v3_ordinal1('#skF_1'(A_217,k1_ordinal1(k3_tarski(A_217))))
      | r1_tarski(A_217,k1_ordinal1(k3_tarski(A_217))) ) ),
    inference(resolution,[status(thm)],[c_1446,c_1787])).

tff(c_1801,plain,
    ( ~ v3_ordinal1(k3_tarski('#skF_7'))
    | r1_tarski('#skF_7',k1_ordinal1(k3_tarski('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_62,c_1793])).

tff(c_1805,plain,(
    r1_tarski('#skF_7',k1_ordinal1(k3_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1801])).

tff(c_42,plain,(
    ! [B_36] :
      ( ~ r1_tarski('#skF_7',B_36)
      | ~ v3_ordinal1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1819,plain,(
    ~ v3_ordinal1(k1_ordinal1(k3_tarski('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_1805,c_42])).

tff(c_1822,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_26,c_1819])).

tff(c_1826,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1822])).

tff(c_1827,plain,(
    v3_ordinal1('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_38,plain,(
    ! [A_31] :
      ( ~ v3_ordinal1('#skF_6'(A_31))
      | v3_ordinal1(k3_tarski(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1828,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_1837,plain,(
    ~ v3_ordinal1('#skF_6'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_38,c_1828])).

tff(c_1841,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1827,c_1837])).

%------------------------------------------------------------------------------
