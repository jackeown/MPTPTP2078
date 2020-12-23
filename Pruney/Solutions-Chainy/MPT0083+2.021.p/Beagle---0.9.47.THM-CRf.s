%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:03 EST 2020

% Result     : Theorem 5.33s
% Output     : CNFRefutation 5.33s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 134 expanded)
%              Number of leaves         :   25 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :   82 ( 149 expanded)
%              Number of equality atoms :   39 (  94 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_19] : r1_xboole_0(A_19,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_134,plain,(
    ! [A_33,B_34,C_35] :
      ( ~ r1_xboole_0(A_33,B_34)
      | ~ r2_hidden(C_35,k3_xboole_0(A_33,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_150,plain,(
    ! [A_10,C_35] :
      ( ~ r1_xboole_0(A_10,k1_xboole_0)
      | ~ r2_hidden(C_35,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_134])).

tff(c_153,plain,(
    ! [C_35] : ~ r2_hidden(C_35,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_150])).

tff(c_12,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_161,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_176,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_161])).

tff(c_179,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_176])).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_164,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k3_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,k4_xboole_0(A_37,B_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_16])).

tff(c_1865,plain,(
    ! [A_98,B_99] : k3_xboole_0(A_98,k4_xboole_0(A_98,B_99)) = k4_xboole_0(A_98,B_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_164])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_279,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_306,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_279])).

tff(c_1913,plain,(
    ! [A_98,B_99] : k4_xboole_0(k4_xboole_0(A_98,B_99),k4_xboole_0(A_98,B_99)) = k4_xboole_0(k4_xboole_0(A_98,B_99),A_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_1865,c_306])).

tff(c_2156,plain,(
    ! [A_103,B_104] : k4_xboole_0(k4_xboole_0(A_103,B_104),A_103) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_1913])).

tff(c_50,plain,(
    ! [B_27,A_28] : k3_xboole_0(B_27,A_28) = k3_xboole_0(A_28,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    ! [A_28] : k3_xboole_0(k1_xboole_0,A_28) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_10])).

tff(c_300,plain,(
    ! [A_28] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_279])).

tff(c_316,plain,(
    ! [A_28] : k4_xboole_0(k1_xboole_0,A_28) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_300])).

tff(c_882,plain,(
    ! [A_74,B_75,C_76] : k2_xboole_0(k4_xboole_0(A_74,B_75),k3_xboole_0(A_74,C_76)) = k4_xboole_0(A_74,k4_xboole_0(B_75,C_76)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_954,plain,(
    ! [A_11,C_76] : k4_xboole_0(A_11,k4_xboole_0(k1_xboole_0,C_76)) = k2_xboole_0(A_11,k3_xboole_0(A_11,C_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_882])).

tff(c_986,plain,(
    ! [A_77,C_78] : k2_xboole_0(A_77,k3_xboole_0(A_77,C_78)) = A_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_316,c_954])).

tff(c_1028,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_986])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_239,plain,(
    ! [A_46,B_47] :
      ( ~ r1_xboole_0(A_46,B_47)
      | k3_xboole_0(A_46,B_47) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_134])).

tff(c_248,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_239])).

tff(c_255,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_2])).

tff(c_927,plain,(
    ! [B_75] : k4_xboole_0('#skF_4',k4_xboole_0(B_75,'#skF_3')) = k2_xboole_0(k4_xboole_0('#skF_4',B_75),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_882])).

tff(c_1719,plain,(
    ! [B_75] : k4_xboole_0('#skF_4',k4_xboole_0(B_75,'#skF_3')) = k4_xboole_0('#skF_4',B_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_927])).

tff(c_2168,plain,(
    ! [B_104] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_3',B_104)) = k4_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2156,c_1719])).

tff(c_2460,plain,(
    ! [B_108] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_3',B_108)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2168])).

tff(c_2487,plain,(
    ! [B_108] : k3_xboole_0('#skF_4',k4_xboole_0('#skF_3',B_108)) = k4_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2460,c_16])).

tff(c_2878,plain,(
    ! [B_112] : k3_xboole_0('#skF_4',k4_xboole_0('#skF_3',B_112)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_2487])).

tff(c_555,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_1'(A_60,B_61),k3_xboole_0(A_60,B_61))
      | r1_xboole_0(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_582,plain,(
    ! [B_2,A_1] :
      ( r2_hidden('#skF_1'(B_2,A_1),k3_xboole_0(A_1,B_2))
      | r1_xboole_0(B_2,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_555])).

tff(c_2889,plain,(
    ! [B_112] :
      ( r2_hidden('#skF_1'(k4_xboole_0('#skF_3',B_112),'#skF_4'),k1_xboole_0)
      | r1_xboole_0(k4_xboole_0('#skF_3',B_112),'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2878,c_582])).

tff(c_2985,plain,(
    ! [B_113] : r1_xboole_0(k4_xboole_0('#skF_3',B_113),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_2889])).

tff(c_3018,plain,(
    ! [B_15] : r1_xboole_0(k3_xboole_0('#skF_3',B_15),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2985])).

tff(c_24,plain,(
    ! [A_20,C_22,B_21] :
      ( r1_xboole_0(A_20,C_22)
      | ~ r1_xboole_0(A_20,k2_xboole_0(B_21,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5950,plain,(
    ! [A_149,A_150,C_151,B_152] :
      ( r1_xboole_0(A_149,k3_xboole_0(A_150,C_151))
      | ~ r1_xboole_0(A_149,k4_xboole_0(A_150,k4_xboole_0(B_152,C_151))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_882,c_24])).

tff(c_6073,plain,(
    ! [A_149,A_150,A_11] :
      ( r1_xboole_0(A_149,k3_xboole_0(A_150,A_11))
      | ~ r1_xboole_0(A_149,k4_xboole_0(A_150,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_5950])).

tff(c_7690,plain,(
    ! [A_171,A_172,A_173] :
      ( r1_xboole_0(A_171,k3_xboole_0(A_172,A_173))
      | ~ r1_xboole_0(A_171,A_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_6073])).

tff(c_28,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_5','#skF_3'),k3_xboole_0('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_31,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_5'),k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_28])).

tff(c_7704,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_7690,c_31])).

tff(c_7793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3018,c_7704])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:45:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.33/2.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.23  
% 5.33/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.23  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 5.33/2.23  
% 5.33/2.23  %Foreground sorts:
% 5.33/2.23  
% 5.33/2.23  
% 5.33/2.23  %Background operators:
% 5.33/2.23  
% 5.33/2.23  
% 5.33/2.23  %Foreground operators:
% 5.33/2.23  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.33/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.33/2.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.33/2.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.33/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.33/2.23  tff('#skF_5', type, '#skF_5': $i).
% 5.33/2.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.33/2.23  tff('#skF_3', type, '#skF_3': $i).
% 5.33/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.33/2.23  tff('#skF_4', type, '#skF_4': $i).
% 5.33/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.33/2.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.33/2.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.33/2.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.33/2.23  
% 5.33/2.24  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.33/2.24  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.33/2.24  tff(f_51, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.33/2.24  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.33/2.24  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.33/2.24  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.33/2.24  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.33/2.24  tff(f_59, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 5.33/2.24  tff(f_82, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 5.33/2.24  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.33/2.24  tff(f_77, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 5.33/2.24  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.33/2.24  tff(c_20, plain, (![A_19]: (r1_xboole_0(A_19, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.33/2.24  tff(c_10, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.33/2.24  tff(c_134, plain, (![A_33, B_34, C_35]: (~r1_xboole_0(A_33, B_34) | ~r2_hidden(C_35, k3_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.33/2.24  tff(c_150, plain, (![A_10, C_35]: (~r1_xboole_0(A_10, k1_xboole_0) | ~r2_hidden(C_35, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_134])).
% 5.33/2.24  tff(c_153, plain, (![C_35]: (~r2_hidden(C_35, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_150])).
% 5.33/2.24  tff(c_12, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.33/2.24  tff(c_161, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.33/2.24  tff(c_176, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_161])).
% 5.33/2.24  tff(c_179, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_176])).
% 5.33/2.24  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.33/2.24  tff(c_164, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k3_xboole_0(A_37, B_38))=k3_xboole_0(A_37, k4_xboole_0(A_37, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_161, c_16])).
% 5.33/2.24  tff(c_1865, plain, (![A_98, B_99]: (k3_xboole_0(A_98, k4_xboole_0(A_98, B_99))=k4_xboole_0(A_98, B_99))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_164])).
% 5.33/2.24  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.33/2.24  tff(c_279, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.33/2.24  tff(c_306, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_279])).
% 5.33/2.24  tff(c_1913, plain, (![A_98, B_99]: (k4_xboole_0(k4_xboole_0(A_98, B_99), k4_xboole_0(A_98, B_99))=k4_xboole_0(k4_xboole_0(A_98, B_99), A_98))), inference(superposition, [status(thm), theory('equality')], [c_1865, c_306])).
% 5.33/2.24  tff(c_2156, plain, (![A_103, B_104]: (k4_xboole_0(k4_xboole_0(A_103, B_104), A_103)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_179, c_1913])).
% 5.33/2.24  tff(c_50, plain, (![B_27, A_28]: (k3_xboole_0(B_27, A_28)=k3_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.33/2.24  tff(c_66, plain, (![A_28]: (k3_xboole_0(k1_xboole_0, A_28)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_10])).
% 5.33/2.24  tff(c_300, plain, (![A_28]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_28))), inference(superposition, [status(thm), theory('equality')], [c_66, c_279])).
% 5.33/2.24  tff(c_316, plain, (![A_28]: (k4_xboole_0(k1_xboole_0, A_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_300])).
% 5.33/2.24  tff(c_882, plain, (![A_74, B_75, C_76]: (k2_xboole_0(k4_xboole_0(A_74, B_75), k3_xboole_0(A_74, C_76))=k4_xboole_0(A_74, k4_xboole_0(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.33/2.24  tff(c_954, plain, (![A_11, C_76]: (k4_xboole_0(A_11, k4_xboole_0(k1_xboole_0, C_76))=k2_xboole_0(A_11, k3_xboole_0(A_11, C_76)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_882])).
% 5.33/2.24  tff(c_986, plain, (![A_77, C_78]: (k2_xboole_0(A_77, k3_xboole_0(A_77, C_78))=A_77)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_316, c_954])).
% 5.33/2.24  tff(c_1028, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(superposition, [status(thm), theory('equality')], [c_10, c_986])).
% 5.33/2.24  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.33/2.24  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.33/2.24  tff(c_239, plain, (![A_46, B_47]: (~r1_xboole_0(A_46, B_47) | k3_xboole_0(A_46, B_47)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_134])).
% 5.33/2.24  tff(c_248, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_239])).
% 5.33/2.24  tff(c_255, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_248, c_2])).
% 5.33/2.24  tff(c_927, plain, (![B_75]: (k4_xboole_0('#skF_4', k4_xboole_0(B_75, '#skF_3'))=k2_xboole_0(k4_xboole_0('#skF_4', B_75), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_255, c_882])).
% 5.33/2.24  tff(c_1719, plain, (![B_75]: (k4_xboole_0('#skF_4', k4_xboole_0(B_75, '#skF_3'))=k4_xboole_0('#skF_4', B_75))), inference(demodulation, [status(thm), theory('equality')], [c_1028, c_927])).
% 5.33/2.24  tff(c_2168, plain, (![B_104]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_3', B_104))=k4_xboole_0('#skF_4', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2156, c_1719])).
% 5.33/2.24  tff(c_2460, plain, (![B_108]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_3', B_108))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2168])).
% 5.33/2.24  tff(c_2487, plain, (![B_108]: (k3_xboole_0('#skF_4', k4_xboole_0('#skF_3', B_108))=k4_xboole_0('#skF_4', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2460, c_16])).
% 5.33/2.24  tff(c_2878, plain, (![B_112]: (k3_xboole_0('#skF_4', k4_xboole_0('#skF_3', B_112))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_179, c_2487])).
% 5.33/2.24  tff(c_555, plain, (![A_60, B_61]: (r2_hidden('#skF_1'(A_60, B_61), k3_xboole_0(A_60, B_61)) | r1_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.33/2.24  tff(c_582, plain, (![B_2, A_1]: (r2_hidden('#skF_1'(B_2, A_1), k3_xboole_0(A_1, B_2)) | r1_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_555])).
% 5.33/2.24  tff(c_2889, plain, (![B_112]: (r2_hidden('#skF_1'(k4_xboole_0('#skF_3', B_112), '#skF_4'), k1_xboole_0) | r1_xboole_0(k4_xboole_0('#skF_3', B_112), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2878, c_582])).
% 5.33/2.24  tff(c_2985, plain, (![B_113]: (r1_xboole_0(k4_xboole_0('#skF_3', B_113), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_153, c_2889])).
% 5.33/2.24  tff(c_3018, plain, (![B_15]: (r1_xboole_0(k3_xboole_0('#skF_3', B_15), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2985])).
% 5.33/2.24  tff(c_24, plain, (![A_20, C_22, B_21]: (r1_xboole_0(A_20, C_22) | ~r1_xboole_0(A_20, k2_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.33/2.24  tff(c_5950, plain, (![A_149, A_150, C_151, B_152]: (r1_xboole_0(A_149, k3_xboole_0(A_150, C_151)) | ~r1_xboole_0(A_149, k4_xboole_0(A_150, k4_xboole_0(B_152, C_151))))), inference(superposition, [status(thm), theory('equality')], [c_882, c_24])).
% 5.33/2.24  tff(c_6073, plain, (![A_149, A_150, A_11]: (r1_xboole_0(A_149, k3_xboole_0(A_150, A_11)) | ~r1_xboole_0(A_149, k4_xboole_0(A_150, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_179, c_5950])).
% 5.33/2.24  tff(c_7690, plain, (![A_171, A_172, A_173]: (r1_xboole_0(A_171, k3_xboole_0(A_172, A_173)) | ~r1_xboole_0(A_171, A_172))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_6073])).
% 5.33/2.24  tff(c_28, plain, (~r1_xboole_0(k3_xboole_0('#skF_5', '#skF_3'), k3_xboole_0('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.33/2.24  tff(c_31, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_5'), k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_28])).
% 5.33/2.24  tff(c_7704, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_7690, c_31])).
% 5.33/2.24  tff(c_7793, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3018, c_7704])).
% 5.33/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.24  
% 5.33/2.24  Inference rules
% 5.33/2.24  ----------------------
% 5.33/2.24  #Ref     : 0
% 5.33/2.24  #Sup     : 1912
% 5.33/2.24  #Fact    : 0
% 5.33/2.24  #Define  : 0
% 5.33/2.24  #Split   : 0
% 5.33/2.24  #Chain   : 0
% 5.33/2.24  #Close   : 0
% 5.33/2.24  
% 5.33/2.24  Ordering : KBO
% 5.33/2.24  
% 5.33/2.24  Simplification rules
% 5.33/2.24  ----------------------
% 5.33/2.24  #Subsume      : 65
% 5.33/2.25  #Demod        : 1743
% 5.33/2.25  #Tautology    : 1361
% 5.33/2.25  #SimpNegUnit  : 40
% 5.33/2.25  #BackRed      : 0
% 5.33/2.25  
% 5.33/2.25  #Partial instantiations: 0
% 5.33/2.25  #Strategies tried      : 1
% 5.33/2.25  
% 5.33/2.25  Timing (in seconds)
% 5.33/2.25  ----------------------
% 5.33/2.25  Preprocessing        : 0.36
% 5.33/2.25  Parsing              : 0.18
% 5.33/2.25  CNF conversion       : 0.03
% 5.33/2.25  Main loop            : 1.06
% 5.33/2.25  Inferencing          : 0.31
% 5.33/2.25  Reduction            : 0.51
% 5.33/2.25  Demodulation         : 0.42
% 5.33/2.25  BG Simplification    : 0.04
% 5.33/2.25  Subsumption          : 0.15
% 5.33/2.25  Abstraction          : 0.05
% 5.33/2.25  MUC search           : 0.00
% 5.33/2.25  Cooper               : 0.00
% 5.33/2.25  Total                : 1.46
% 5.33/2.25  Index Insertion      : 0.00
% 5.33/2.25  Index Deletion       : 0.00
% 5.33/2.25  Index Matching       : 0.00
% 5.33/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
