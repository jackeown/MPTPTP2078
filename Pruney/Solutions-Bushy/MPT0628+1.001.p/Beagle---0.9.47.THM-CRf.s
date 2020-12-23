%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0628+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:36 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 303 expanded)
%              Number of leaves         :   19 ( 122 expanded)
%              Depth                    :   17
%              Number of atoms          :  157 (1200 expanded)
%              Number of equality atoms :   21 ( 217 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( r2_hidden(A,k1_relat_1(B))
             => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_69,axiom,(
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

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_8,plain,(
    ! [A_1,B_4] :
      ( k1_funct_1(A_1,B_4) = k1_xboole_0
      | r2_hidden(B_4,k1_relat_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,(
    ! [A_34,C_35,B_36] :
      ( r2_hidden(A_34,k1_relat_1(k5_relat_1(C_35,B_36)))
      | ~ r2_hidden(k1_funct_1(C_35,A_34),k1_relat_1(B_36))
      | ~ r2_hidden(A_34,k1_relat_1(C_35))
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35)
      | ~ v1_funct_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_91,plain,(
    ! [A_40,C_41,A_42] :
      ( r2_hidden(A_40,k1_relat_1(k5_relat_1(C_41,A_42)))
      | ~ r2_hidden(A_40,k1_relat_1(C_41))
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41)
      | k1_funct_1(A_42,k1_funct_1(C_41,A_40)) = k1_xboole_0
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(resolution,[status(thm)],[c_8,c_65])).

tff(c_20,plain,(
    ! [C_15,B_13,A_12] :
      ( k1_funct_1(k5_relat_1(C_15,B_13),A_12) = k1_funct_1(B_13,k1_funct_1(C_15,A_12))
      | ~ r2_hidden(A_12,k1_relat_1(k5_relat_1(C_15,B_13)))
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_175,plain,(
    ! [C_58,A_59,A_60] :
      ( k1_funct_1(k5_relat_1(C_58,A_59),A_60) = k1_funct_1(A_59,k1_funct_1(C_58,A_60))
      | ~ r2_hidden(A_60,k1_relat_1(C_58))
      | ~ v1_funct_1(C_58)
      | ~ v1_relat_1(C_58)
      | k1_funct_1(A_59,k1_funct_1(C_58,A_60)) = k1_xboole_0
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(resolution,[status(thm)],[c_91,c_20])).

tff(c_188,plain,(
    ! [A_59] :
      ( k1_funct_1(k5_relat_1('#skF_2',A_59),'#skF_1') = k1_funct_1(A_59,k1_funct_1('#skF_2','#skF_1'))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | k1_funct_1(A_59,k1_funct_1('#skF_2','#skF_1')) = k1_xboole_0
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(resolution,[status(thm)],[c_24,c_175])).

tff(c_197,plain,(
    ! [A_61] :
      ( k1_funct_1(k5_relat_1('#skF_2',A_61),'#skF_1') = k1_funct_1(A_61,k1_funct_1('#skF_2','#skF_1'))
      | k1_funct_1(A_61,k1_funct_1('#skF_2','#skF_1')) = k1_xboole_0
      | ~ v1_funct_1(A_61)
      | ~ v1_relat_1(A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_188])).

tff(c_22,plain,(
    k1_funct_1(k5_relat_1('#skF_2','#skF_3'),'#skF_1') != k1_funct_1('#skF_3',k1_funct_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_215,plain,
    ( k1_funct_1('#skF_3',k1_funct_1('#skF_2','#skF_1')) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_22])).

tff(c_228,plain,(
    k1_funct_1('#skF_3',k1_funct_1('#skF_2','#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_215])).

tff(c_232,plain,(
    k1_funct_1(k5_relat_1('#skF_2','#skF_3'),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_22])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( v1_funct_1(k5_relat_1(A_6,B_7))
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k5_relat_1(A_6,B_7))
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ! [C_11,A_8,B_9] :
      ( r2_hidden(k1_funct_1(C_11,A_8),k1_relat_1(B_9))
      | ~ r2_hidden(A_8,k1_relat_1(k5_relat_1(C_11,B_9)))
      | ~ v1_funct_1(C_11)
      | ~ v1_relat_1(C_11)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [B_4,A_1] :
      ( r2_hidden(k4_tarski(B_4,k1_funct_1(A_1,B_4)),A_1)
      | ~ r2_hidden(B_4,k1_relat_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_242,plain,
    ( r2_hidden(k4_tarski(k1_funct_1('#skF_2','#skF_1'),k1_xboole_0),'#skF_3')
    | ~ r2_hidden(k1_funct_1('#skF_2','#skF_1'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_4])).

tff(c_250,plain,
    ( r2_hidden(k4_tarski(k1_funct_1('#skF_2','#skF_1'),k1_xboole_0),'#skF_3')
    | ~ r2_hidden(k1_funct_1('#skF_2','#skF_1'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_242])).

tff(c_262,plain,(
    ~ r2_hidden(k1_funct_1('#skF_2','#skF_1'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_268,plain,
    ( ~ r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_262])).

tff(c_277,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_32,c_30,c_268])).

tff(c_289,plain,
    ( k1_funct_1(k5_relat_1('#skF_2','#skF_3'),'#skF_1') = k1_xboole_0
    | ~ v1_funct_1(k5_relat_1('#skF_2','#skF_3'))
    | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_277])).

tff(c_296,plain,
    ( ~ v1_funct_1(k5_relat_1('#skF_2','#skF_3'))
    | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_289])).

tff(c_297,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_300,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_297])).

tff(c_304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_300])).

tff(c_305,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_314,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_305])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_314])).

tff(c_320,plain,(
    r2_hidden(k1_funct_1('#skF_2','#skF_1'),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_14,plain,(
    ! [A_8,C_11,B_9] :
      ( r2_hidden(A_8,k1_relat_1(k5_relat_1(C_11,B_9)))
      | ~ r2_hidden(k1_funct_1(C_11,A_8),k1_relat_1(B_9))
      | ~ r2_hidden(A_8,k1_relat_1(C_11))
      | ~ v1_funct_1(C_11)
      | ~ v1_relat_1(C_11)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_325,plain,
    ( r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_320,c_14])).

tff(c_331,plain,(
    r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_32,c_30,c_24,c_325])).

tff(c_336,plain,
    ( k1_funct_1(k5_relat_1('#skF_2','#skF_3'),'#skF_1') = k1_funct_1('#skF_3',k1_funct_1('#skF_2','#skF_1'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_331,c_20])).

tff(c_343,plain,(
    k1_funct_1(k5_relat_1('#skF_2','#skF_3'),'#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_32,c_30,c_228,c_336])).

tff(c_345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_343])).

%------------------------------------------------------------------------------
