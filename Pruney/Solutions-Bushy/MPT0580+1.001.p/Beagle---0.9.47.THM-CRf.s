%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0580+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:32 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   49 (  75 expanded)
%              Number of leaves         :   19 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :   66 ( 139 expanded)
%              Number of equality atoms :   13 (  30 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v3_relat_1 > v1_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v3_relat_1,type,(
    v3_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( v3_relat_1(A)
        <=> ! [B] :
              ( r2_hidden(B,k2_relat_1(A))
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v3_relat_1(A)
      <=> r1_tarski(k2_relat_1(A),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_relat_1)).

tff(c_26,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ v3_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_37,plain,(
    ~ v3_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_36,plain,(
    ! [B_14] :
      ( v3_relat_1('#skF_4')
      | k1_xboole_0 = B_14
      | ~ r2_hidden(B_14,k2_relat_1('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_53,plain,(
    ! [B_20] :
      ( k1_xboole_0 = B_20
      | ~ r2_hidden(B_20,k2_relat_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_36])).

tff(c_107,plain,(
    ! [B_35] :
      ( '#skF_3'(k2_relat_1('#skF_4'),B_35) = k1_xboole_0
      | r1_tarski(k2_relat_1('#skF_4'),B_35) ) ),
    inference(resolution,[status(thm)],[c_22,c_53])).

tff(c_2,plain,(
    ! [A_1] :
      ( v3_relat_1(A_1)
      | ~ r1_tarski(k2_relat_1(A_1),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_111,plain,
    ( v3_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_3'(k2_relat_1('#skF_4'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_107,c_2])).

tff(c_114,plain,
    ( v3_relat_1('#skF_4')
    | '#skF_3'(k2_relat_1('#skF_4'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_111])).

tff(c_115,plain,(
    '#skF_3'(k2_relat_1('#skF_4'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_114])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_119,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | r1_tarski(k2_relat_1('#skF_4'),k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_20])).

tff(c_126,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_119])).

tff(c_130,plain,
    ( v3_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_126,c_2])).

tff(c_133,plain,(
    v3_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_130])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_133])).

tff(c_136,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_137,plain,(
    v3_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_179,plain,(
    ! [A_48] :
      ( r1_tarski(k2_relat_1(A_48),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_28,plain,
    ( r2_hidden('#skF_5',k2_relat_1('#skF_4'))
    | ~ v3_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_140,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_28])).

tff(c_162,plain,(
    ! [C_44,B_45,A_46] :
      ( r2_hidden(C_44,B_45)
      | ~ r2_hidden(C_44,A_46)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_170,plain,(
    ! [B_45] :
      ( r2_hidden('#skF_5',B_45)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_45) ) ),
    inference(resolution,[status(thm)],[c_140,c_162])).

tff(c_183,plain,
    ( r2_hidden('#skF_5',k1_tarski(k1_xboole_0))
    | ~ v3_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_179,c_170])).

tff(c_186,plain,(
    r2_hidden('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_137,c_183])).

tff(c_6,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_191,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_186,c_6])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_191])).

%------------------------------------------------------------------------------
