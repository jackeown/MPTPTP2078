%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:09 EST 2020

% Result     : Theorem 12.26s
% Output     : CNFRefutation 12.35s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 547 expanded)
%              Number of leaves         :   24 ( 188 expanded)
%              Depth                    :   13
%              Number of atoms          :  169 (1511 expanded)
%              Number of equality atoms :   21 ( 138 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_107,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_103,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_56,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_52,plain,(
    ! [A_37] :
      ( v3_ordinal1(k1_ordinal1(A_37))
      | ~ v3_ordinal1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_54,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_737,plain,(
    ! [B_128,A_129] :
      ( r2_hidden(B_128,A_129)
      | r1_ordinal1(A_129,B_128)
      | ~ v3_ordinal1(B_128)
      | ~ v3_ordinal1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_64,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_93,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_58,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_143,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_58])).

tff(c_800,plain,
    ( r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_737,c_143])).

tff(c_840,plain,(
    r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_800])).

tff(c_40,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ r1_ordinal1(A_29,B_30)
      | ~ v3_ordinal1(B_30)
      | ~ v3_ordinal1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_651,plain,(
    ! [A_121,B_122] :
      ( r1_tarski(A_121,B_122)
      | ~ r1_ordinal1(A_121,B_122)
      | ~ v3_ordinal1(B_122)
      | ~ v3_ordinal1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3271,plain,(
    ! [B_253,A_254] :
      ( B_253 = A_254
      | ~ r1_tarski(B_253,A_254)
      | ~ r1_ordinal1(A_254,B_253)
      | ~ v3_ordinal1(B_253)
      | ~ v3_ordinal1(A_254) ) ),
    inference(resolution,[status(thm)],[c_651,c_4])).

tff(c_15779,plain,(
    ! [B_625,A_626] :
      ( B_625 = A_626
      | ~ r1_ordinal1(B_625,A_626)
      | ~ r1_ordinal1(A_626,B_625)
      | ~ v3_ordinal1(B_625)
      | ~ v3_ordinal1(A_626) ) ),
    inference(resolution,[status(thm)],[c_40,c_3271])).

tff(c_15805,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_840,c_15779])).

tff(c_15823,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_15805])).

tff(c_15827,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_15823])).

tff(c_15807,plain,
    ( k1_ordinal1('#skF_1') = '#skF_2'
    | ~ r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_93,c_15779])).

tff(c_15826,plain,
    ( k1_ordinal1('#skF_1') = '#skF_2'
    | ~ r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_15807])).

tff(c_15831,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_15826])).

tff(c_15834,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_15831])).

tff(c_15838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_15834])).

tff(c_15840,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_15826])).

tff(c_36,plain,(
    ! [A_28] : k2_xboole_0(A_28,k1_tarski(A_28)) = k1_ordinal1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_5869,plain,(
    ! [A_354,B_355,B_356] :
      ( r1_tarski(A_354,B_355)
      | ~ r1_ordinal1(k2_xboole_0(A_354,B_356),B_355)
      | ~ v3_ordinal1(B_355)
      | ~ v3_ordinal1(k2_xboole_0(A_354,B_356)) ) ),
    inference(resolution,[status(thm)],[c_651,c_10])).

tff(c_5882,plain,(
    ! [A_28,B_355] :
      ( r1_tarski(A_28,B_355)
      | ~ r1_ordinal1(k1_ordinal1(A_28),B_355)
      | ~ v3_ordinal1(B_355)
      | ~ v3_ordinal1(k2_xboole_0(A_28,k1_tarski(A_28))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_5869])).

tff(c_15845,plain,(
    ! [A_627,B_628] :
      ( r1_tarski(A_627,B_628)
      | ~ r1_ordinal1(k1_ordinal1(A_627),B_628)
      | ~ v3_ordinal1(B_628)
      | ~ v3_ordinal1(k1_ordinal1(A_627)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5882])).

tff(c_15883,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_93,c_15845])).

tff(c_15898,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15840,c_54,c_15883])).

tff(c_38,plain,(
    ! [A_29,B_30] :
      ( r1_ordinal1(A_29,B_30)
      | ~ r1_tarski(A_29,B_30)
      | ~ v3_ordinal1(B_30)
      | ~ v3_ordinal1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_15910,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_15898,c_38])).

tff(c_15920,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_15910])).

tff(c_15922,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15827,c_15920])).

tff(c_15923,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_15823])).

tff(c_15926,plain,(
    ~ r2_hidden('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15923,c_143])).

tff(c_16987,plain,
    ( k1_ordinal1('#skF_1') = '#skF_1'
    | ~ r1_ordinal1('#skF_1',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15923,c_15923,c_15826])).

tff(c_16988,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_16987])).

tff(c_16991,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_16988])).

tff(c_16995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_16991])).

tff(c_16997,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_16987])).

tff(c_46,plain,(
    ! [B_33] : r2_hidden(B_33,k1_ordinal1(B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2156,plain,(
    ! [A_207,B_208] :
      ( ~ r2_hidden(A_207,B_208)
      | r1_ordinal1(A_207,B_208)
      | ~ v3_ordinal1(B_208)
      | ~ v3_ordinal1(A_207) ) ),
    inference(resolution,[status(thm)],[c_737,c_2])).

tff(c_2236,plain,(
    ! [B_33] :
      ( r1_ordinal1(B_33,k1_ordinal1(B_33))
      | ~ v3_ordinal1(k1_ordinal1(B_33))
      | ~ v3_ordinal1(B_33) ) ),
    inference(resolution,[status(thm)],[c_46,c_2156])).

tff(c_16996,plain,
    ( ~ r1_ordinal1('#skF_1',k1_ordinal1('#skF_1'))
    | k1_ordinal1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16987])).

tff(c_16998,plain,(
    ~ r1_ordinal1('#skF_1',k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_16996])).

tff(c_17003,plain,
    ( ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2236,c_16998])).

tff(c_17007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_16997,c_17003])).

tff(c_17008,plain,(
    k1_ordinal1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16996])).

tff(c_17384,plain,(
    r2_hidden('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_17008,c_46])).

tff(c_17459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15926,c_17384])).

tff(c_17460,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_17464,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_17460,c_2])).

tff(c_18638,plain,(
    ! [B_745,A_746] :
      ( r2_hidden(B_745,A_746)
      | r1_ordinal1(A_746,B_745)
      | ~ v3_ordinal1(B_745)
      | ~ v3_ordinal1(A_746) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_44,plain,(
    ! [B_33,A_32] :
      ( B_33 = A_32
      | r2_hidden(A_32,B_33)
      | ~ r2_hidden(A_32,k1_ordinal1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_22967,plain,(
    ! [B_916,B_915] :
      ( B_916 = B_915
      | r2_hidden(B_915,B_916)
      | r1_ordinal1(k1_ordinal1(B_916),B_915)
      | ~ v3_ordinal1(B_915)
      | ~ v3_ordinal1(k1_ordinal1(B_916)) ) ),
    inference(resolution,[status(thm)],[c_18638,c_44])).

tff(c_17461,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_22970,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22967,c_17461])).

tff(c_22973,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_22970])).

tff(c_22974,plain,
    ( '#skF_2' = '#skF_1'
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_17464,c_22973])).

tff(c_22975,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_22974])).

tff(c_22978,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_22975])).

tff(c_22982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_22978])).

tff(c_22983,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_22974])).

tff(c_23013,plain,(
    r2_hidden('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22983,c_17460])).

tff(c_23026,plain,(
    ~ r2_hidden('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_23013,c_2])).

tff(c_23034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23013,c_23026])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:50:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.26/4.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.26/4.57  
% 12.26/4.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.26/4.57  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 12.26/4.57  
% 12.26/4.57  %Foreground sorts:
% 12.26/4.57  
% 12.26/4.57  
% 12.26/4.57  %Background operators:
% 12.26/4.57  
% 12.26/4.57  
% 12.26/4.57  %Foreground operators:
% 12.26/4.57  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 12.26/4.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.26/4.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.26/4.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.26/4.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.26/4.57  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 12.26/4.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.26/4.57  tff('#skF_2', type, '#skF_2': $i).
% 12.26/4.57  tff('#skF_1', type, '#skF_1': $i).
% 12.26/4.57  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 12.26/4.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.26/4.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.26/4.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.26/4.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.26/4.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.26/4.57  
% 12.35/4.59  tff(f_117, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 12.35/4.59  tff(f_107, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 12.35/4.59  tff(f_103, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 12.35/4.59  tff(f_86, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 12.35/4.59  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.35/4.59  tff(f_78, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 12.35/4.59  tff(f_40, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 12.35/4.59  tff(f_94, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 12.35/4.59  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 12.35/4.59  tff(c_56, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.35/4.59  tff(c_52, plain, (![A_37]: (v3_ordinal1(k1_ordinal1(A_37)) | ~v3_ordinal1(A_37))), inference(cnfTransformation, [status(thm)], [f_107])).
% 12.35/4.59  tff(c_54, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.35/4.59  tff(c_737, plain, (![B_128, A_129]: (r2_hidden(B_128, A_129) | r1_ordinal1(A_129, B_128) | ~v3_ordinal1(B_128) | ~v3_ordinal1(A_129))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.35/4.59  tff(c_64, plain, (r2_hidden('#skF_1', '#skF_2') | r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.35/4.59  tff(c_93, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_64])).
% 12.35/4.59  tff(c_58, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.35/4.59  tff(c_143, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_58])).
% 12.35/4.59  tff(c_800, plain, (r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_737, c_143])).
% 12.35/4.59  tff(c_840, plain, (r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_800])).
% 12.35/4.59  tff(c_40, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | ~r1_ordinal1(A_29, B_30) | ~v3_ordinal1(B_30) | ~v3_ordinal1(A_29))), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.35/4.59  tff(c_651, plain, (![A_121, B_122]: (r1_tarski(A_121, B_122) | ~r1_ordinal1(A_121, B_122) | ~v3_ordinal1(B_122) | ~v3_ordinal1(A_121))), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.35/4.59  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.35/4.59  tff(c_3271, plain, (![B_253, A_254]: (B_253=A_254 | ~r1_tarski(B_253, A_254) | ~r1_ordinal1(A_254, B_253) | ~v3_ordinal1(B_253) | ~v3_ordinal1(A_254))), inference(resolution, [status(thm)], [c_651, c_4])).
% 12.35/4.59  tff(c_15779, plain, (![B_625, A_626]: (B_625=A_626 | ~r1_ordinal1(B_625, A_626) | ~r1_ordinal1(A_626, B_625) | ~v3_ordinal1(B_625) | ~v3_ordinal1(A_626))), inference(resolution, [status(thm)], [c_40, c_3271])).
% 12.35/4.59  tff(c_15805, plain, ('#skF_2'='#skF_1' | ~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_840, c_15779])).
% 12.35/4.59  tff(c_15823, plain, ('#skF_2'='#skF_1' | ~r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_15805])).
% 12.35/4.59  tff(c_15827, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_15823])).
% 12.35/4.59  tff(c_15807, plain, (k1_ordinal1('#skF_1')='#skF_2' | ~r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_93, c_15779])).
% 12.35/4.59  tff(c_15826, plain, (k1_ordinal1('#skF_1')='#skF_2' | ~r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_15807])).
% 12.35/4.59  tff(c_15831, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_15826])).
% 12.35/4.59  tff(c_15834, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_52, c_15831])).
% 12.35/4.59  tff(c_15838, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_15834])).
% 12.35/4.59  tff(c_15840, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_15826])).
% 12.35/4.59  tff(c_36, plain, (![A_28]: (k2_xboole_0(A_28, k1_tarski(A_28))=k1_ordinal1(A_28))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.35/4.59  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.35/4.59  tff(c_5869, plain, (![A_354, B_355, B_356]: (r1_tarski(A_354, B_355) | ~r1_ordinal1(k2_xboole_0(A_354, B_356), B_355) | ~v3_ordinal1(B_355) | ~v3_ordinal1(k2_xboole_0(A_354, B_356)))), inference(resolution, [status(thm)], [c_651, c_10])).
% 12.35/4.59  tff(c_5882, plain, (![A_28, B_355]: (r1_tarski(A_28, B_355) | ~r1_ordinal1(k1_ordinal1(A_28), B_355) | ~v3_ordinal1(B_355) | ~v3_ordinal1(k2_xboole_0(A_28, k1_tarski(A_28))))), inference(superposition, [status(thm), theory('equality')], [c_36, c_5869])).
% 12.35/4.59  tff(c_15845, plain, (![A_627, B_628]: (r1_tarski(A_627, B_628) | ~r1_ordinal1(k1_ordinal1(A_627), B_628) | ~v3_ordinal1(B_628) | ~v3_ordinal1(k1_ordinal1(A_627)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_5882])).
% 12.35/4.59  tff(c_15883, plain, (r1_tarski('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_93, c_15845])).
% 12.35/4.59  tff(c_15898, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15840, c_54, c_15883])).
% 12.35/4.59  tff(c_38, plain, (![A_29, B_30]: (r1_ordinal1(A_29, B_30) | ~r1_tarski(A_29, B_30) | ~v3_ordinal1(B_30) | ~v3_ordinal1(A_29))), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.35/4.59  tff(c_15910, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_15898, c_38])).
% 12.35/4.59  tff(c_15920, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_15910])).
% 12.35/4.59  tff(c_15922, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15827, c_15920])).
% 12.35/4.59  tff(c_15923, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_15823])).
% 12.35/4.59  tff(c_15926, plain, (~r2_hidden('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15923, c_143])).
% 12.35/4.59  tff(c_16987, plain, (k1_ordinal1('#skF_1')='#skF_1' | ~r1_ordinal1('#skF_1', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_15923, c_15923, c_15826])).
% 12.35/4.59  tff(c_16988, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_16987])).
% 12.35/4.59  tff(c_16991, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_52, c_16988])).
% 12.35/4.59  tff(c_16995, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_16991])).
% 12.35/4.59  tff(c_16997, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_16987])).
% 12.35/4.59  tff(c_46, plain, (![B_33]: (r2_hidden(B_33, k1_ordinal1(B_33)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.35/4.59  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 12.35/4.59  tff(c_2156, plain, (![A_207, B_208]: (~r2_hidden(A_207, B_208) | r1_ordinal1(A_207, B_208) | ~v3_ordinal1(B_208) | ~v3_ordinal1(A_207))), inference(resolution, [status(thm)], [c_737, c_2])).
% 12.35/4.59  tff(c_2236, plain, (![B_33]: (r1_ordinal1(B_33, k1_ordinal1(B_33)) | ~v3_ordinal1(k1_ordinal1(B_33)) | ~v3_ordinal1(B_33))), inference(resolution, [status(thm)], [c_46, c_2156])).
% 12.35/4.59  tff(c_16996, plain, (~r1_ordinal1('#skF_1', k1_ordinal1('#skF_1')) | k1_ordinal1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_16987])).
% 12.35/4.59  tff(c_16998, plain, (~r1_ordinal1('#skF_1', k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_16996])).
% 12.35/4.59  tff(c_17003, plain, (~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_2236, c_16998])).
% 12.35/4.59  tff(c_17007, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_16997, c_17003])).
% 12.35/4.59  tff(c_17008, plain, (k1_ordinal1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_16996])).
% 12.35/4.59  tff(c_17384, plain, (r2_hidden('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_17008, c_46])).
% 12.35/4.59  tff(c_17459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15926, c_17384])).
% 12.35/4.59  tff(c_17460, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 12.35/4.59  tff(c_17464, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_17460, c_2])).
% 12.35/4.59  tff(c_18638, plain, (![B_745, A_746]: (r2_hidden(B_745, A_746) | r1_ordinal1(A_746, B_745) | ~v3_ordinal1(B_745) | ~v3_ordinal1(A_746))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.35/4.59  tff(c_44, plain, (![B_33, A_32]: (B_33=A_32 | r2_hidden(A_32, B_33) | ~r2_hidden(A_32, k1_ordinal1(B_33)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.35/4.59  tff(c_22967, plain, (![B_916, B_915]: (B_916=B_915 | r2_hidden(B_915, B_916) | r1_ordinal1(k1_ordinal1(B_916), B_915) | ~v3_ordinal1(B_915) | ~v3_ordinal1(k1_ordinal1(B_916)))), inference(resolution, [status(thm)], [c_18638, c_44])).
% 12.35/4.59  tff(c_17461, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 12.35/4.59  tff(c_22970, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_22967, c_17461])).
% 12.35/4.59  tff(c_22973, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_22970])).
% 12.35/4.59  tff(c_22974, plain, ('#skF_2'='#skF_1' | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_17464, c_22973])).
% 12.35/4.59  tff(c_22975, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_22974])).
% 12.35/4.59  tff(c_22978, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_52, c_22975])).
% 12.35/4.59  tff(c_22982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_22978])).
% 12.35/4.59  tff(c_22983, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_22974])).
% 12.35/4.59  tff(c_23013, plain, (r2_hidden('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22983, c_17460])).
% 12.35/4.59  tff(c_23026, plain, (~r2_hidden('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_23013, c_2])).
% 12.35/4.59  tff(c_23034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23013, c_23026])).
% 12.35/4.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.35/4.59  
% 12.35/4.59  Inference rules
% 12.35/4.59  ----------------------
% 12.35/4.59  #Ref     : 0
% 12.35/4.59  #Sup     : 5082
% 12.35/4.59  #Fact    : 2
% 12.35/4.59  #Define  : 0
% 12.35/4.59  #Split   : 9
% 12.35/4.59  #Chain   : 0
% 12.35/4.59  #Close   : 0
% 12.35/4.59  
% 12.35/4.59  Ordering : KBO
% 12.35/4.59  
% 12.35/4.59  Simplification rules
% 12.35/4.59  ----------------------
% 12.35/4.59  #Subsume      : 552
% 12.35/4.59  #Demod        : 1863
% 12.35/4.59  #Tautology    : 1422
% 12.35/4.59  #SimpNegUnit  : 3
% 12.35/4.59  #BackRed      : 60
% 12.35/4.59  
% 12.35/4.59  #Partial instantiations: 0
% 12.35/4.59  #Strategies tried      : 1
% 12.35/4.59  
% 12.35/4.59  Timing (in seconds)
% 12.35/4.59  ----------------------
% 12.35/4.59  Preprocessing        : 0.31
% 12.35/4.59  Parsing              : 0.16
% 12.35/4.59  CNF conversion       : 0.02
% 12.35/4.59  Main loop            : 3.43
% 12.35/4.59  Inferencing          : 0.80
% 12.35/4.59  Reduction            : 1.44
% 12.35/4.59  Demodulation         : 1.06
% 12.35/4.59  BG Simplification    : 0.09
% 12.35/4.59  Subsumption          : 0.83
% 12.35/4.59  Abstraction          : 0.11
% 12.35/4.59  MUC search           : 0.00
% 12.35/4.59  Cooper               : 0.00
% 12.35/4.59  Total                : 3.78
% 12.35/4.59  Index Insertion      : 0.00
% 12.35/4.59  Index Deletion       : 0.00
% 12.35/4.59  Index Matching       : 0.00
% 12.35/4.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
