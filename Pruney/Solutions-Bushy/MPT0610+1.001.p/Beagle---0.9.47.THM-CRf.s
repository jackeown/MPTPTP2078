%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0610+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:35 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   47 (  84 expanded)
%              Number of leaves         :   23 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   70 ( 195 expanded)
%              Number of equality atoms :    3 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_6 > #skF_1 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_7 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_8'(A_40,B_41),A_40)
      | r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_8'(A_40,B_41),B_41)
      | r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_97,plain,(
    ! [A_68,B_69] :
      ( k4_tarski('#skF_2'(A_68,B_69),'#skF_3'(A_68,B_69)) = B_69
      | ~ r2_hidden(B_69,A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [C_34,A_19,D_37] :
      ( r2_hidden(C_34,k1_relat_1(A_19))
      | ~ r2_hidden(k4_tarski(C_34,D_37),A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_103,plain,(
    ! [A_68,B_69,A_19] :
      ( r2_hidden('#skF_2'(A_68,B_69),k1_relat_1(A_19))
      | ~ r2_hidden(B_69,A_19)
      | ~ r2_hidden(B_69,A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_10])).

tff(c_126,plain,(
    ! [A_77,B_78,A_79] :
      ( r2_hidden('#skF_2'(A_77,B_78),k1_relat_1(A_79))
      | ~ r2_hidden(B_78,A_79)
      | ~ r2_hidden(B_78,A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_10])).

tff(c_30,plain,(
    r1_xboole_0(k1_relat_1('#skF_9'),k1_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_47,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,B_57)
      | ~ r2_hidden(C_58,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_53,plain,(
    ! [C_58] :
      ( ~ r2_hidden(C_58,k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_58,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_30,c_47])).

tff(c_133,plain,(
    ! [A_83,B_84] :
      ( ~ r2_hidden('#skF_2'(A_83,B_84),k1_relat_1('#skF_9'))
      | ~ r2_hidden(B_84,'#skF_10')
      | ~ r2_hidden(B_84,A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(resolution,[status(thm)],[c_126,c_53])).

tff(c_139,plain,(
    ! [B_85,A_86] :
      ( ~ r2_hidden(B_85,'#skF_10')
      | ~ r2_hidden(B_85,'#skF_9')
      | ~ r2_hidden(B_85,A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(resolution,[status(thm)],[c_103,c_133])).

tff(c_161,plain,(
    ! [B_87,A_88] :
      ( ~ r2_hidden('#skF_8'('#skF_10',B_87),'#skF_9')
      | ~ r2_hidden('#skF_8'('#skF_10',B_87),A_88)
      | ~ v1_relat_1(A_88)
      | r1_xboole_0('#skF_10',B_87) ) ),
    inference(resolution,[status(thm)],[c_26,c_139])).

tff(c_165,plain,(
    ! [A_88] :
      ( ~ r2_hidden('#skF_8'('#skF_10','#skF_9'),A_88)
      | ~ v1_relat_1(A_88)
      | r1_xboole_0('#skF_10','#skF_9') ) ),
    inference(resolution,[status(thm)],[c_24,c_161])).

tff(c_168,plain,(
    ! [A_90] :
      ( ~ r2_hidden('#skF_8'('#skF_10','#skF_9'),A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_172,plain,
    ( ~ v1_relat_1('#skF_10')
    | r1_xboole_0('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_168])).

tff(c_179,plain,(
    r1_xboole_0('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_172])).

tff(c_20,plain,(
    ! [B_39,A_38] :
      ( r1_xboole_0(B_39,A_38)
      | ~ r1_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_186,plain,(
    r1_xboole_0('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_179,c_20])).

tff(c_191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_186])).

tff(c_192,plain,(
    r1_xboole_0('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_196,plain,(
    r1_xboole_0('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_192,c_20])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_196])).

%------------------------------------------------------------------------------
