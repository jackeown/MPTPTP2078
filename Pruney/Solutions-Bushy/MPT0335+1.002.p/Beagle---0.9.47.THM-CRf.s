%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0335+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:07 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 217 expanded)
%              Number of leaves         :   23 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          :   85 ( 459 expanded)
%              Number of equality atoms :   21 ( 164 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_46,plain,(
    r2_hidden('#skF_8','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [C_7] : r2_hidden(C_7,k1_tarski(C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_48,plain,(
    k3_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_93,plain,(
    ! [D_35,B_36,A_37] :
      ( r2_hidden(D_35,B_36)
      | ~ r2_hidden(D_35,k3_xboole_0(A_37,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_103,plain,(
    ! [D_38] :
      ( r2_hidden(D_38,'#skF_7')
      | ~ r2_hidden(D_38,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_93])).

tff(c_108,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_103])).

tff(c_44,plain,(
    k3_xboole_0('#skF_5','#skF_7') != k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_50,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_123,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_tarski(k3_xboole_0(A_41,C_42),k3_xboole_0(B_43,C_42))
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_174,plain,(
    ! [A_48] :
      ( r1_tarski(k3_xboole_0(A_48,'#skF_7'),k1_tarski('#skF_8'))
      | ~ r1_tarski(A_48,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_123])).

tff(c_34,plain,(
    ! [B_15,A_14] :
      ( k1_tarski(B_15) = A_14
      | k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_tarski(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_231,plain,(
    ! [A_54] :
      ( k3_xboole_0(A_54,'#skF_7') = k1_tarski('#skF_8')
      | k3_xboole_0(A_54,'#skF_7') = k1_xboole_0
      | ~ r1_tarski(A_54,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_174,c_34])).

tff(c_234,plain,
    ( k3_xboole_0('#skF_5','#skF_7') = k1_tarski('#skF_8')
    | k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_231])).

tff(c_237,plain,(
    k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_234])).

tff(c_16,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,k3_xboole_0(A_8,B_9))
      | ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_296,plain,(
    ! [D_59] :
      ( r2_hidden(D_59,k1_xboole_0)
      | ~ r2_hidden(D_59,'#skF_7')
      | ~ r2_hidden(D_59,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_16])).

tff(c_42,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_79,plain,(
    ! [D_29,A_30,B_31] :
      ( r2_hidden(D_29,A_30)
      | ~ r2_hidden(D_29,k3_xboole_0(A_30,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_85,plain,(
    ! [D_29,A_19] :
      ( r2_hidden(D_29,A_19)
      | ~ r2_hidden(D_29,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_79])).

tff(c_564,plain,(
    ! [D_626,A_627] :
      ( r2_hidden(D_626,A_627)
      | ~ r2_hidden(D_626,'#skF_7')
      | ~ r2_hidden(D_626,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_296,c_85])).

tff(c_569,plain,(
    ! [A_627] :
      ( r2_hidden('#skF_8',A_627)
      | ~ r2_hidden('#skF_8','#skF_5') ) ),
    inference(resolution,[status(thm)],[c_108,c_564])).

tff(c_573,plain,(
    ! [A_627] : r2_hidden('#skF_8',A_627) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_569])).

tff(c_588,plain,(
    ! [A_629] : r2_hidden('#skF_8',A_629) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_569])).

tff(c_4,plain,(
    ! [C_7,A_3] :
      ( C_7 = A_3
      | ~ r2_hidden(C_7,k1_tarski(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_640,plain,(
    ! [A_630] : A_630 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_588,c_4])).

tff(c_320,plain,(
    ! [D_61,A_62] :
      ( r2_hidden(D_61,A_62)
      | ~ r2_hidden(D_61,'#skF_7')
      | ~ r2_hidden(D_61,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_296,c_85])).

tff(c_322,plain,(
    ! [A_62] :
      ( r2_hidden('#skF_8',A_62)
      | ~ r2_hidden('#skF_8','#skF_5') ) ),
    inference(resolution,[status(thm)],[c_108,c_320])).

tff(c_325,plain,(
    ! [A_62] : r2_hidden('#skF_8',A_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_322])).

tff(c_329,plain,(
    ! [A_63] : r2_hidden('#skF_8',A_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_322])).

tff(c_381,plain,(
    ! [A_64] : A_64 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_329,c_4])).

tff(c_65,plain,(
    ! [B_24,A_25] :
      ( ~ r2_hidden(B_24,A_25)
      | ~ r2_hidden(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70,plain,(
    ! [C_7] : ~ r2_hidden(k1_tarski(C_7),C_7) ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_316,plain,
    ( ~ r2_hidden(k1_tarski(k1_xboole_0),'#skF_7')
    | ~ r2_hidden(k1_tarski(k1_xboole_0),'#skF_5') ),
    inference(resolution,[status(thm)],[c_296,c_70])).

tff(c_318,plain,(
    ~ r2_hidden(k1_tarski(k1_xboole_0),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_316])).

tff(c_387,plain,(
    ~ r2_hidden('#skF_8','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_318])).

tff(c_520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_387])).

tff(c_522,plain,(
    r2_hidden(k1_tarski(k1_xboole_0),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_563,plain,(
    ~ r2_hidden('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_522,c_2])).

tff(c_650,plain,(
    ~ r2_hidden('#skF_8',k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_563])).

tff(c_793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_650])).

%------------------------------------------------------------------------------
