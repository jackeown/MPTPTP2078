%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0664+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:40 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 161 expanded)
%              Number of leaves         :   20 (  68 expanded)
%              Depth                    :   12
%              Number of atoms          :  109 ( 487 expanded)
%              Number of equality atoms :   22 ( 115 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,B)
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(c_26,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8,plain,(
    ! [A_1,B_4] :
      ( k1_funct_1(A_1,B_4) = k1_xboole_0
      | r2_hidden(B_4,k1_relat_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    ! [A_13,C_15,B_14] :
      ( r2_hidden(A_13,k1_relat_1(k7_relat_1(C_15,B_14)))
      | ~ r2_hidden(A_13,k1_relat_1(C_15))
      | ~ r2_hidden(A_13,B_14)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_82,plain,(
    ! [C_36,B_37,A_38] :
      ( k1_funct_1(k7_relat_1(C_36,B_37),A_38) = k1_funct_1(C_36,A_38)
      | ~ r2_hidden(A_38,k1_relat_1(k7_relat_1(C_36,B_37)))
      | ~ v1_funct_1(C_36)
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_105,plain,(
    ! [C_45,B_46,A_47] :
      ( k1_funct_1(k7_relat_1(C_45,B_46),A_47) = k1_funct_1(C_45,A_47)
      | ~ v1_funct_1(C_45)
      | ~ r2_hidden(A_47,k1_relat_1(C_45))
      | ~ r2_hidden(A_47,B_46)
      | ~ v1_relat_1(C_45) ) ),
    inference(resolution,[status(thm)],[c_18,c_82])).

tff(c_133,plain,(
    ! [A_51,B_52,B_53] :
      ( k1_funct_1(k7_relat_1(A_51,B_52),B_53) = k1_funct_1(A_51,B_53)
      | ~ r2_hidden(B_53,B_52)
      | k1_funct_1(A_51,B_53) = k1_xboole_0
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(resolution,[status(thm)],[c_8,c_105])).

tff(c_24,plain,(
    k1_funct_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k1_funct_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_145,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | k1_funct_1('#skF_3','#skF_1') = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_24])).

tff(c_155,plain,(
    k1_funct_1('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_145])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( v1_funct_1(k7_relat_1(A_8,B_9))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_40,plain,(
    ! [A_25,C_26,B_27] :
      ( r2_hidden(A_25,k1_relat_1(C_26))
      | ~ r2_hidden(A_25,k1_relat_1(k7_relat_1(C_26,B_27)))
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_185,plain,(
    ! [B_54,C_55,B_56] :
      ( r2_hidden(B_54,k1_relat_1(C_55))
      | ~ v1_relat_1(C_55)
      | k1_funct_1(k7_relat_1(C_55,B_56),B_54) = k1_xboole_0
      | ~ v1_funct_1(k7_relat_1(C_55,B_56))
      | ~ v1_relat_1(k7_relat_1(C_55,B_56)) ) ),
    inference(resolution,[status(thm)],[c_8,c_40])).

tff(c_189,plain,(
    ! [B_57,A_58,B_59] :
      ( r2_hidden(B_57,k1_relat_1(A_58))
      | k1_funct_1(k7_relat_1(A_58,B_59),B_57) = k1_xboole_0
      | ~ v1_funct_1(k7_relat_1(A_58,B_59))
      | ~ v1_relat_1(A_58) ) ),
    inference(resolution,[status(thm)],[c_10,c_185])).

tff(c_193,plain,(
    ! [B_60,A_61,B_62] :
      ( r2_hidden(B_60,k1_relat_1(A_61))
      | k1_funct_1(k7_relat_1(A_61,B_62),B_60) = k1_xboole_0
      | ~ v1_funct_1(A_61)
      | ~ v1_relat_1(A_61) ) ),
    inference(resolution,[status(thm)],[c_12,c_189])).

tff(c_4,plain,(
    ! [B_4,A_1] :
      ( r2_hidden(k4_tarski(B_4,k1_funct_1(A_1,B_4)),A_1)
      | ~ r2_hidden(B_4,k1_relat_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_161,plain,
    ( r2_hidden(k4_tarski('#skF_1',k1_xboole_0),'#skF_3')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_4])).

tff(c_165,plain,
    ( r2_hidden(k4_tarski('#skF_1',k1_xboole_0),'#skF_3')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_161])).

tff(c_178,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_196,plain,(
    ! [B_62] :
      ( k1_funct_1(k7_relat_1('#skF_3',B_62),'#skF_1') = k1_xboole_0
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_193,c_178])).

tff(c_239,plain,(
    ! [B_62] : k1_funct_1(k7_relat_1('#skF_3',B_62),'#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_196])).

tff(c_157,plain,(
    k1_funct_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_24])).

tff(c_255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_157])).

tff(c_257,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_94,plain,(
    ! [C_15,B_14,A_13] :
      ( k1_funct_1(k7_relat_1(C_15,B_14),A_13) = k1_funct_1(C_15,A_13)
      | ~ v1_funct_1(C_15)
      | ~ r2_hidden(A_13,k1_relat_1(C_15))
      | ~ r2_hidden(A_13,B_14)
      | ~ v1_relat_1(C_15) ) ),
    inference(resolution,[status(thm)],[c_18,c_82])).

tff(c_259,plain,(
    ! [B_14] :
      ( k1_funct_1(k7_relat_1('#skF_3',B_14),'#skF_1') = k1_funct_1('#skF_3','#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden('#skF_1',B_14)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_257,c_94])).

tff(c_269,plain,(
    ! [B_66] :
      ( k1_funct_1(k7_relat_1('#skF_3',B_66),'#skF_1') = k1_xboole_0
      | ~ r2_hidden('#skF_1',B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_155,c_259])).

tff(c_275,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_157])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_275])).

%------------------------------------------------------------------------------
