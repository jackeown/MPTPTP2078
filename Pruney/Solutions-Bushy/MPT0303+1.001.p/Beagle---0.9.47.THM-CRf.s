%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0303+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:04 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 200 expanded)
%              Number of leaves         :   15 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :   87 ( 412 expanded)
%              Number of equality atoms :   19 ( 100 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_43,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,A) = k2_zfmisc_1(B,B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_18,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r2_hidden('#skF_2'(A_5,B_6),A_5)
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_56,plain,(
    ! [A_28,B_29,C_30,D_31] :
      ( r2_hidden(k4_tarski(A_28,B_29),k2_zfmisc_1(C_30,D_31))
      | ~ r2_hidden(B_29,D_31)
      | ~ r2_hidden(A_28,C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    k2_zfmisc_1('#skF_3','#skF_3') = k2_zfmisc_1('#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_33,plain,(
    ! [A_12,C_13,B_14,D_15] :
      ( r2_hidden(A_12,C_13)
      | ~ r2_hidden(k4_tarski(A_12,B_14),k2_zfmisc_1(C_13,D_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [A_12,B_14] :
      ( r2_hidden(A_12,'#skF_3')
      | ~ r2_hidden(k4_tarski(A_12,B_14),k2_zfmisc_1('#skF_4','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_33])).

tff(c_74,plain,(
    ! [A_28,B_29] :
      ( r2_hidden(A_28,'#skF_3')
      | ~ r2_hidden(B_29,'#skF_4')
      | ~ r2_hidden(A_28,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_36])).

tff(c_79,plain,(
    ! [B_32] : ~ r2_hidden(B_32,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_91,plain,(
    ! [B_6] :
      ( r2_hidden('#skF_1'('#skF_4',B_6),B_6)
      | B_6 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_16,c_79])).

tff(c_78,plain,(
    ! [B_29] : ~ r2_hidden(B_29,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_103,plain,(
    ! [A_34,B_35] :
      ( r2_hidden(k4_tarski(A_34,B_35),k2_zfmisc_1('#skF_4','#skF_4'))
      | ~ r2_hidden(B_35,'#skF_3')
      | ~ r2_hidden(A_34,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_56])).

tff(c_8,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,(
    ! [A_34,B_35] :
      ( r2_hidden(A_34,'#skF_4')
      | ~ r2_hidden(B_35,'#skF_3')
      | ~ r2_hidden(A_34,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_103,c_8])).

tff(c_120,plain,(
    ! [B_35,A_34] :
      ( ~ r2_hidden(B_35,'#skF_3')
      | ~ r2_hidden(A_34,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_112])).

tff(c_127,plain,(
    ! [A_36] : ~ r2_hidden(A_36,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_131,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_91,c_127])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_131])).

tff(c_149,plain,(
    ! [B_37] : ~ r2_hidden(B_37,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_153,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_91,c_149])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_153])).

tff(c_186,plain,(
    ! [A_40] :
      ( r2_hidden(A_40,'#skF_3')
      | ~ r2_hidden(A_40,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_306,plain,(
    ! [A_49] :
      ( r2_hidden('#skF_1'(A_49,'#skF_3'),'#skF_3')
      | A_49 = '#skF_3'
      | ~ r2_hidden('#skF_2'(A_49,'#skF_3'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_186,c_12])).

tff(c_318,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_3'),'#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16,c_306])).

tff(c_325,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_18,c_318])).

tff(c_169,plain,(
    ! [A_38,B_39] :
      ( r2_hidden(k4_tarski(A_38,B_39),k2_zfmisc_1('#skF_4','#skF_4'))
      | ~ r2_hidden(B_39,'#skF_3')
      | ~ r2_hidden(A_38,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_56])).

tff(c_6,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_185,plain,(
    ! [B_39,A_38] :
      ( r2_hidden(B_39,'#skF_4')
      | ~ r2_hidden(B_39,'#skF_3')
      | ~ r2_hidden(A_38,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_169,c_6])).

tff(c_196,plain,(
    ! [A_38] : ~ r2_hidden(A_38,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_168,plain,(
    ! [A_28] :
      ( r2_hidden(A_28,'#skF_3')
      | ~ r2_hidden(A_28,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_213,plain,(
    ! [A_42] : ~ r2_hidden(A_42,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_168])).

tff(c_232,plain,(
    ! [B_45] :
      ( r2_hidden('#skF_1'('#skF_4',B_45),B_45)
      | B_45 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_16,c_213])).

tff(c_240,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_232,c_196])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_240])).

tff(c_250,plain,(
    ! [B_39] :
      ( r2_hidden(B_39,'#skF_4')
      | ~ r2_hidden(B_39,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_329,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_325,c_250])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r2_hidden('#skF_2'(A_5,B_6),A_5)
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6),A_5)
      | ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_331,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_3'),'#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_329,c_10])).

tff(c_334,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_331])).

tff(c_338,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_168,c_334])).

tff(c_341,plain,
    ( ~ r2_hidden('#skF_1'('#skF_4','#skF_3'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_14,c_338])).

tff(c_347,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_341])).

tff(c_349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_347])).

%------------------------------------------------------------------------------
