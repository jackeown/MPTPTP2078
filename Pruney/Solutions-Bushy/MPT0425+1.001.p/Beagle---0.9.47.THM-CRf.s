%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0425+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:17 EST 2020

% Result     : Theorem 38.78s
% Output     : CNFRefutation 38.83s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 132 expanded)
%              Number of leaves         :   25 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  100 ( 221 expanded)
%              Number of equality atoms :   23 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(C,k3_tarski(k2_xboole_0(A,B)))
          & ! [D] :
              ( r2_hidden(D,B)
             => r1_xboole_0(D,C) ) )
       => r1_tarski(C,k3_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_xboole_0(C,B) )
     => r1_xboole_0(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_4',k3_tarski('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    ! [A_28,B_29] : r1_tarski(k3_xboole_0(A_28,B_29),A_28) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_52,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_49])).

tff(c_20,plain,(
    ! [A_19,B_20] : k2_xboole_0(k3_tarski(A_19),k3_tarski(B_20)) = k3_tarski(k2_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_114,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_1'(A_40,B_41),A_40)
      | r1_xboole_0(k3_tarski(A_40),B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    ! [D_25] :
      ( r1_xboole_0(D_25,'#skF_4')
      | ~ r2_hidden(D_25,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_337,plain,(
    ! [B_68] :
      ( r1_xboole_0('#skF_1'('#skF_3',B_68),'#skF_4')
      | r1_xboole_0(k3_tarski('#skF_3'),B_68) ) ),
    inference(resolution,[status(thm)],[c_114,c_28])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_636,plain,(
    ! [B_91] :
      ( k3_xboole_0(k3_tarski('#skF_3'),B_91) = k1_xboole_0
      | r1_xboole_0('#skF_1'('#skF_3',B_91),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_337,c_4])).

tff(c_22,plain,(
    ! [A_21,B_22] :
      ( ~ r1_xboole_0('#skF_1'(A_21,B_22),B_22)
      | r1_xboole_0(k3_tarski(A_21),B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_639,plain,
    ( r1_xboole_0(k3_tarski('#skF_3'),'#skF_4')
    | k3_xboole_0(k3_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_636,c_22])).

tff(c_644,plain,
    ( r1_xboole_0(k3_tarski('#skF_3'),'#skF_4')
    | k3_xboole_0('#skF_4',k3_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_639])).

tff(c_647,plain,(
    k3_xboole_0('#skF_4',k3_tarski('#skF_3')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_644])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] : k2_xboole_0(k3_xboole_0(A_16,B_17),k3_xboole_0(A_16,C_18)) = k3_xboole_0(A_16,k2_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_660,plain,(
    ! [B_17] : k3_xboole_0('#skF_4',k2_xboole_0(B_17,k3_tarski('#skF_3'))) = k2_xboole_0(k3_xboole_0('#skF_4',B_17),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_18])).

tff(c_12108,plain,(
    ! [B_343] : k3_xboole_0('#skF_4',k2_xboole_0(B_343,k3_tarski('#skF_3'))) = k3_xboole_0('#skF_4',B_343) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_660])).

tff(c_101519,plain,(
    ! [A_989] : k3_xboole_0('#skF_4',k3_tarski(k2_xboole_0(A_989,'#skF_3'))) = k3_xboole_0('#skF_4',k3_tarski(A_989)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_12108])).

tff(c_30,plain,(
    r1_tarski('#skF_4',k3_tarski(k2_xboole_0('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_317,plain,(
    ! [A_65,B_66,C_67] :
      ( r1_tarski(A_65,k3_xboole_0(B_66,C_67))
      | ~ r1_tarski(A_65,C_67)
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_13,C_15,B_14] :
      ( r1_tarski(A_13,C_15)
      | ~ r1_tarski(B_14,C_15)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2527,plain,(
    ! [A_152,B_153,C_154,A_155] :
      ( r1_tarski(A_152,k3_xboole_0(B_153,C_154))
      | ~ r1_tarski(A_152,A_155)
      | ~ r1_tarski(A_155,C_154)
      | ~ r1_tarski(A_155,B_153) ) ),
    inference(resolution,[status(thm)],[c_317,c_16])).

tff(c_10303,plain,(
    ! [A_295,B_296,B_297,C_298] :
      ( r1_tarski(k3_xboole_0(A_295,B_296),k3_xboole_0(B_297,C_298))
      | ~ r1_tarski(A_295,C_298)
      | ~ r1_tarski(A_295,B_297) ) ),
    inference(resolution,[status(thm)],[c_10,c_2527])).

tff(c_55,plain,(
    ! [B_32,A_33] : k3_xboole_0(B_32,A_33) = k3_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_70,plain,(
    ! [B_32,A_33] : r1_tarski(k3_xboole_0(B_32,A_33),A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_10])).

tff(c_129,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_tarski(A_44,C_45)
      | ~ r1_tarski(B_46,C_45)
      | ~ r1_tarski(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_139,plain,(
    ! [A_44,A_33,B_32] :
      ( r1_tarski(A_44,A_33)
      | ~ r1_tarski(A_44,k3_xboole_0(B_32,A_33)) ) ),
    inference(resolution,[status(thm)],[c_70,c_129])).

tff(c_42596,plain,(
    ! [A_635,B_636,C_637,B_638] :
      ( r1_tarski(k3_xboole_0(A_635,B_636),C_637)
      | ~ r1_tarski(A_635,C_637)
      | ~ r1_tarski(A_635,B_638) ) ),
    inference(resolution,[status(thm)],[c_10303,c_139])).

tff(c_43227,plain,(
    ! [B_639,C_640] :
      ( r1_tarski(k3_xboole_0('#skF_4',B_639),C_640)
      | ~ r1_tarski('#skF_4',C_640) ) ),
    inference(resolution,[status(thm)],[c_30,c_42596])).

tff(c_333,plain,(
    ! [A_13,B_66,C_67,A_65] :
      ( r1_tarski(A_13,k3_xboole_0(B_66,C_67))
      | ~ r1_tarski(A_13,A_65)
      | ~ r1_tarski(A_65,C_67)
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_317,c_16])).

tff(c_76539,plain,(
    ! [B_848,B_849,C_850,C_851] :
      ( r1_tarski(k3_xboole_0('#skF_4',B_848),k3_xboole_0(B_849,C_850))
      | ~ r1_tarski(C_851,C_850)
      | ~ r1_tarski(C_851,B_849)
      | ~ r1_tarski('#skF_4',C_851) ) ),
    inference(resolution,[status(thm)],[c_43227,c_333])).

tff(c_77079,plain,(
    ! [B_848,B_849] :
      ( r1_tarski(k3_xboole_0('#skF_4',B_848),k3_xboole_0(B_849,k3_tarski(k2_xboole_0('#skF_2','#skF_3'))))
      | ~ r1_tarski('#skF_4',B_849)
      | ~ r1_tarski('#skF_4','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_76539])).

tff(c_77367,plain,(
    ! [B_848,B_849] :
      ( r1_tarski(k3_xboole_0('#skF_4',B_848),k3_xboole_0(B_849,k3_tarski(k2_xboole_0('#skF_2','#skF_3'))))
      | ~ r1_tarski('#skF_4',B_849) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_77079])).

tff(c_101596,plain,(
    ! [B_848] :
      ( r1_tarski(k3_xboole_0('#skF_4',B_848),k3_xboole_0('#skF_4',k3_tarski('#skF_2')))
      | ~ r1_tarski('#skF_4','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101519,c_77367])).

tff(c_102933,plain,(
    ! [B_993] : r1_tarski(k3_xboole_0('#skF_4',B_993),k3_xboole_0('#skF_4',k3_tarski('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_101596])).

tff(c_103046,plain,(
    ! [B_994] : r1_tarski(k3_xboole_0('#skF_4',B_994),k3_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_102933,c_139])).

tff(c_103122,plain,(
    r1_tarski('#skF_4',k3_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_103046])).

tff(c_103140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_103122])).

tff(c_103142,plain,(
    k3_xboole_0('#skF_4',k3_tarski('#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_644])).

tff(c_103141,plain,(
    r1_xboole_0(k3_tarski('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_644])).

tff(c_103146,plain,(
    k3_xboole_0(k3_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_103141,c_4])).

tff(c_103236,plain,(
    k3_xboole_0('#skF_4',k3_tarski('#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_103146,c_2])).

tff(c_103253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103142,c_103236])).

%------------------------------------------------------------------------------
