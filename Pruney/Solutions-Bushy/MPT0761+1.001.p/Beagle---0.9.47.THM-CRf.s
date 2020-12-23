%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0761+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:49 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   53 (  82 expanded)
%              Number of leaves         :   20 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :  111 ( 205 expanded)
%              Number of equality atoms :   22 (  30 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_wellord1 > r1_tarski > v1_wellord1 > v1_relat_1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r1_wellord1,type,(
    r1_wellord1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( v1_wellord1(A)
        <=> r1_wellord1(A,k3_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_wellord1(A,B)
        <=> ! [C] :
              ~ ( r1_tarski(C,B)
                & C != k1_xboole_0
                & ! [D] :
                    ~ ( r2_hidden(D,C)
                      & r1_xboole_0(k1_wellord1(A,D),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_wellord1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_wellord1(A)
      <=> ! [B] :
            ~ ( r1_tarski(B,k3_relat_1(A))
              & B != k1_xboole_0
              & ! [C] :
                  ~ ( r2_hidden(C,B)
                    & r1_xboole_0(k1_wellord1(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_wellord1)).

tff(c_22,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_98,plain,(
    ! [A_64,B_65] :
      ( '#skF_3'(A_64,B_65) != k1_xboole_0
      | r1_wellord1(A_64,B_65)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,
    ( ~ r1_wellord1('#skF_5',k3_relat_1('#skF_5'))
    | ~ v1_wellord1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_31,plain,(
    ~ v1_wellord1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_33,plain,(
    ! [A_37] :
      ( '#skF_2'(A_37) != k1_xboole_0
      | v1_wellord1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,
    ( '#skF_2'('#skF_5') != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_33,c_31])).

tff(c_39,plain,(
    '#skF_2'('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_36])).

tff(c_30,plain,
    ( v1_wellord1('#skF_5')
    | r1_wellord1('#skF_5',k3_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    r1_wellord1('#skF_5',k3_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_30])).

tff(c_6,plain,(
    ! [A_1] :
      ( r1_tarski('#skF_2'(A_1),k3_relat_1(A_1))
      | v1_wellord1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_12,B_26,C_35] :
      ( r2_hidden('#skF_4'(A_12,B_26,C_35),C_35)
      | k1_xboole_0 = C_35
      | ~ r1_tarski(C_35,B_26)
      | ~ r1_wellord1(A_12,B_26)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_58,plain,(
    ! [A_55,B_56,C_57] :
      ( r1_xboole_0(k1_wellord1(A_55,'#skF_4'(A_55,B_56,C_57)),C_57)
      | k1_xboole_0 = C_57
      | ~ r1_tarski(C_57,B_56)
      | ~ r1_wellord1(A_55,B_56)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [A_1,C_11] :
      ( ~ r1_xboole_0(k1_wellord1(A_1,C_11),'#skF_2'(A_1))
      | ~ r2_hidden(C_11,'#skF_2'(A_1))
      | v1_wellord1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_69,plain,(
    ! [A_58,B_59] :
      ( ~ r2_hidden('#skF_4'(A_58,B_59,'#skF_2'(A_58)),'#skF_2'(A_58))
      | v1_wellord1(A_58)
      | '#skF_2'(A_58) = k1_xboole_0
      | ~ r1_tarski('#skF_2'(A_58),B_59)
      | ~ r1_wellord1(A_58,B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(resolution,[status(thm)],[c_58,c_2])).

tff(c_75,plain,(
    ! [A_60,B_61] :
      ( v1_wellord1(A_60)
      | '#skF_2'(A_60) = k1_xboole_0
      | ~ r1_tarski('#skF_2'(A_60),B_61)
      | ~ r1_wellord1(A_60,B_61)
      | ~ v1_relat_1(A_60) ) ),
    inference(resolution,[status(thm)],[c_14,c_69])).

tff(c_80,plain,(
    ! [A_62] :
      ( '#skF_2'(A_62) = k1_xboole_0
      | ~ r1_wellord1(A_62,k3_relat_1(A_62))
      | v1_wellord1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_87,plain,
    ( '#skF_2'('#skF_5') = k1_xboole_0
    | v1_wellord1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_80])).

tff(c_91,plain,
    ( '#skF_2'('#skF_5') = k1_xboole_0
    | v1_wellord1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_87])).

tff(c_93,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_39,c_91])).

tff(c_94,plain,(
    ~ r1_wellord1('#skF_5',k3_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_101,plain,
    ( '#skF_3'('#skF_5',k3_relat_1('#skF_5')) != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_98,c_94])).

tff(c_104,plain,(
    '#skF_3'('#skF_5',k3_relat_1('#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_101])).

tff(c_95,plain,(
    v1_wellord1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_20,plain,(
    ! [A_12,B_26] :
      ( r1_tarski('#skF_3'(A_12,B_26),B_26)
      | r1_wellord1(A_12,B_26)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [A_1,B_8] :
      ( r2_hidden('#skF_1'(A_1,B_8),B_8)
      | k1_xboole_0 = B_8
      | ~ r1_tarski(B_8,k3_relat_1(A_1))
      | ~ v1_wellord1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_111,plain,(
    ! [A_79,B_80] :
      ( r1_xboole_0(k1_wellord1(A_79,'#skF_1'(A_79,B_80)),B_80)
      | k1_xboole_0 = B_80
      | ~ r1_tarski(B_80,k3_relat_1(A_79))
      | ~ v1_wellord1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_12,D_34,B_26] :
      ( ~ r1_xboole_0(k1_wellord1(A_12,D_34),'#skF_3'(A_12,B_26))
      | ~ r2_hidden(D_34,'#skF_3'(A_12,B_26))
      | r1_wellord1(A_12,B_26)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_150,plain,(
    ! [A_89,B_90] :
      ( ~ r2_hidden('#skF_1'(A_89,'#skF_3'(A_89,B_90)),'#skF_3'(A_89,B_90))
      | r1_wellord1(A_89,B_90)
      | '#skF_3'(A_89,B_90) = k1_xboole_0
      | ~ r1_tarski('#skF_3'(A_89,B_90),k3_relat_1(A_89))
      | ~ v1_wellord1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(resolution,[status(thm)],[c_111,c_16])).

tff(c_157,plain,(
    ! [A_92,B_93] :
      ( r1_wellord1(A_92,B_93)
      | '#skF_3'(A_92,B_93) = k1_xboole_0
      | ~ r1_tarski('#skF_3'(A_92,B_93),k3_relat_1(A_92))
      | ~ v1_wellord1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(resolution,[status(thm)],[c_10,c_150])).

tff(c_163,plain,(
    ! [A_94] :
      ( '#skF_3'(A_94,k3_relat_1(A_94)) = k1_xboole_0
      | ~ v1_wellord1(A_94)
      | r1_wellord1(A_94,k3_relat_1(A_94))
      | ~ v1_relat_1(A_94) ) ),
    inference(resolution,[status(thm)],[c_20,c_157])).

tff(c_169,plain,
    ( '#skF_3'('#skF_5',k3_relat_1('#skF_5')) = k1_xboole_0
    | ~ v1_wellord1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_163,c_94])).

tff(c_173,plain,(
    '#skF_3'('#skF_5',k3_relat_1('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_95,c_169])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_173])).

%------------------------------------------------------------------------------
