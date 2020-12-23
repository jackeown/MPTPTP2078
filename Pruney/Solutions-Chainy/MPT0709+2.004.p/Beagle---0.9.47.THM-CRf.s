%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:25 EST 2020

% Result     : Theorem 20.91s
% Output     : CNFRefutation 21.05s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 161 expanded)
%              Number of leaves         :   30 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  135 ( 359 expanded)
%              Number of equality atoms :   31 (  81 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k10_relat_1(B,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_38,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_46,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_103,plain,(
    ! [A_37,B_38] : k1_setfam_1(k2_tarski(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_163,plain,(
    ! [B_44,A_45] : k1_setfam_1(k2_tarski(B_44,A_45)) = k3_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_103])).

tff(c_14,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_169,plain,(
    ! [B_44,A_45] : k3_xboole_0(B_44,A_45) = k3_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_14])).

tff(c_926,plain,(
    ! [B_96,A_97] :
      ( r1_tarski(k10_relat_1(B_96,k9_relat_1(B_96,A_97)),A_97)
      | ~ v2_funct_1(B_96)
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_943,plain,(
    ! [B_96,A_97] :
      ( k3_xboole_0(k10_relat_1(B_96,k9_relat_1(B_96,A_97)),A_97) = k10_relat_1(B_96,k9_relat_1(B_96,A_97))
      | ~ v2_funct_1(B_96)
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(resolution,[status(thm)],[c_926,c_10])).

tff(c_6971,plain,(
    ! [A_248,B_249] :
      ( k3_xboole_0(A_248,k10_relat_1(B_249,k9_relat_1(B_249,A_248))) = k10_relat_1(B_249,k9_relat_1(B_249,A_248))
      | ~ v2_funct_1(B_249)
      | ~ v1_funct_1(B_249)
      | ~ v1_relat_1(B_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_943])).

tff(c_34,plain,(
    ! [A_23,C_25,B_24] :
      ( k3_xboole_0(A_23,k10_relat_1(C_25,B_24)) = k10_relat_1(k7_relat_1(C_25,A_23),B_24)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_62279,plain,(
    ! [B_793,A_794] :
      ( k10_relat_1(k7_relat_1(B_793,A_794),k9_relat_1(B_793,A_794)) = k10_relat_1(B_793,k9_relat_1(B_793,A_794))
      | ~ v1_relat_1(B_793)
      | ~ v2_funct_1(B_793)
      | ~ v1_funct_1(B_793)
      | ~ v1_relat_1(B_793) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6971,c_34])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_118,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = A_39
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_125,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_42,c_118])).

tff(c_22,plain,(
    ! [A_18] :
      ( k10_relat_1(A_18,k2_relat_1(A_18)) = k1_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_593,plain,(
    ! [A_77,C_78,B_79] :
      ( k3_xboole_0(A_77,k10_relat_1(C_78,B_79)) = k10_relat_1(k7_relat_1(C_78,A_77),B_79)
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2445,plain,(
    ! [A_149,A_150] :
      ( k10_relat_1(k7_relat_1(A_149,A_150),k2_relat_1(A_149)) = k3_xboole_0(A_150,k1_relat_1(A_149))
      | ~ v1_relat_1(A_149)
      | ~ v1_relat_1(A_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_593])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k10_relat_1(B_17,A_16),k1_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6217,plain,(
    ! [A_235,A_236] :
      ( r1_tarski(k3_xboole_0(A_235,k1_relat_1(A_236)),k1_relat_1(k7_relat_1(A_236,A_235)))
      | ~ v1_relat_1(k7_relat_1(A_236,A_235))
      | ~ v1_relat_1(A_236)
      | ~ v1_relat_1(A_236) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2445,c_20])).

tff(c_6293,plain,
    ( r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_6217])).

tff(c_6325,plain,
    ( r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_6293])).

tff(c_6328,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_6325])).

tff(c_6331,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_6328])).

tff(c_6335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6331])).

tff(c_6337,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_6325])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_389,plain,(
    ! [B_62,A_63] :
      ( r1_tarski(k10_relat_1(B_62,A_63),k10_relat_1(B_62,k2_relat_1(B_62)))
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4273,plain,(
    ! [B_193,A_194,A_195] :
      ( r1_tarski(k10_relat_1(k7_relat_1(B_193,A_194),A_195),k10_relat_1(k7_relat_1(B_193,A_194),k9_relat_1(B_193,A_194)))
      | ~ v1_relat_1(k7_relat_1(B_193,A_194))
      | ~ v1_relat_1(B_193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_389])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_413,plain,(
    ! [B_62,A_63] :
      ( k10_relat_1(B_62,k2_relat_1(B_62)) = k10_relat_1(B_62,A_63)
      | ~ r1_tarski(k10_relat_1(B_62,k2_relat_1(B_62)),k10_relat_1(B_62,A_63))
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_389,c_2])).

tff(c_4345,plain,(
    ! [B_193,A_194] :
      ( k10_relat_1(k7_relat_1(B_193,A_194),k2_relat_1(k7_relat_1(B_193,A_194))) = k10_relat_1(k7_relat_1(B_193,A_194),k9_relat_1(B_193,A_194))
      | ~ v1_relat_1(k7_relat_1(B_193,A_194))
      | ~ v1_relat_1(B_193) ) ),
    inference(resolution,[status(thm)],[c_4273,c_413])).

tff(c_24,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k10_relat_1(B_20,A_19),k10_relat_1(B_20,k2_relat_1(B_20)))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_9475,plain,(
    ! [A_293,A_294] :
      ( r1_tarski(k3_xboole_0(A_293,k1_relat_1(A_294)),k10_relat_1(k7_relat_1(A_294,A_293),k2_relat_1(k7_relat_1(A_294,A_293))))
      | ~ v1_relat_1(k7_relat_1(A_294,A_293))
      | ~ v1_relat_1(A_294)
      | ~ v1_relat_1(A_294) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2445,c_24])).

tff(c_9607,plain,
    ( r1_tarski('#skF_1',k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_9475])).

tff(c_9659,plain,(
    r1_tarski('#skF_1',k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_6337,c_9607])).

tff(c_9778,plain,
    ( r1_tarski('#skF_1',k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4345,c_9659])).

tff(c_9807,plain,(
    r1_tarski('#skF_1',k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6337,c_9778])).

tff(c_62469,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_62279,c_9807])).

tff(c_62714,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_46,c_62469])).

tff(c_952,plain,(
    ! [B_96,A_97] :
      ( k10_relat_1(B_96,k9_relat_1(B_96,A_97)) = A_97
      | ~ r1_tarski(A_97,k10_relat_1(B_96,k9_relat_1(B_96,A_97)))
      | ~ v2_funct_1(B_96)
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(resolution,[status(thm)],[c_926,c_2])).

tff(c_62794,plain,
    ( k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62714,c_952])).

tff(c_62844,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_62794])).

tff(c_62846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_62844])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:11:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.91/12.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.91/12.64  
% 20.91/12.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.91/12.64  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 20.91/12.64  
% 20.91/12.64  %Foreground sorts:
% 20.91/12.64  
% 20.91/12.64  
% 20.91/12.64  %Background operators:
% 20.91/12.64  
% 20.91/12.64  
% 20.91/12.64  %Foreground operators:
% 20.91/12.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 20.91/12.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 20.91/12.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.91/12.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 20.91/12.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.91/12.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 20.91/12.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.91/12.64  tff('#skF_2', type, '#skF_2': $i).
% 20.91/12.64  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 20.91/12.64  tff('#skF_1', type, '#skF_1': $i).
% 20.91/12.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.91/12.64  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 20.91/12.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 20.91/12.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 20.91/12.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.91/12.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 20.91/12.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 20.91/12.64  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 20.91/12.64  
% 21.05/12.66  tff(f_96, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 21.05/12.66  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 21.05/12.66  tff(f_45, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 21.05/12.66  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 21.05/12.66  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 21.05/12.66  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 21.05/12.66  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 21.05/12.66  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 21.05/12.66  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 21.05/12.66  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 21.05/12.66  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k10_relat_1(B, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t170_relat_1)).
% 21.05/12.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 21.05/12.66  tff(c_38, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_96])).
% 21.05/12.66  tff(c_46, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 21.05/12.66  tff(c_44, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 21.05/12.66  tff(c_40, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 21.05/12.66  tff(c_12, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 21.05/12.66  tff(c_103, plain, (![A_37, B_38]: (k1_setfam_1(k2_tarski(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 21.05/12.66  tff(c_163, plain, (![B_44, A_45]: (k1_setfam_1(k2_tarski(B_44, A_45))=k3_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_12, c_103])).
% 21.05/12.66  tff(c_14, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 21.05/12.66  tff(c_169, plain, (![B_44, A_45]: (k3_xboole_0(B_44, A_45)=k3_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_163, c_14])).
% 21.05/12.66  tff(c_926, plain, (![B_96, A_97]: (r1_tarski(k10_relat_1(B_96, k9_relat_1(B_96, A_97)), A_97) | ~v2_funct_1(B_96) | ~v1_funct_1(B_96) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_85])).
% 21.05/12.66  tff(c_10, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 21.05/12.66  tff(c_943, plain, (![B_96, A_97]: (k3_xboole_0(k10_relat_1(B_96, k9_relat_1(B_96, A_97)), A_97)=k10_relat_1(B_96, k9_relat_1(B_96, A_97)) | ~v2_funct_1(B_96) | ~v1_funct_1(B_96) | ~v1_relat_1(B_96))), inference(resolution, [status(thm)], [c_926, c_10])).
% 21.05/12.66  tff(c_6971, plain, (![A_248, B_249]: (k3_xboole_0(A_248, k10_relat_1(B_249, k9_relat_1(B_249, A_248)))=k10_relat_1(B_249, k9_relat_1(B_249, A_248)) | ~v2_funct_1(B_249) | ~v1_funct_1(B_249) | ~v1_relat_1(B_249))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_943])).
% 21.05/12.66  tff(c_34, plain, (![A_23, C_25, B_24]: (k3_xboole_0(A_23, k10_relat_1(C_25, B_24))=k10_relat_1(k7_relat_1(C_25, A_23), B_24) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 21.05/12.66  tff(c_62279, plain, (![B_793, A_794]: (k10_relat_1(k7_relat_1(B_793, A_794), k9_relat_1(B_793, A_794))=k10_relat_1(B_793, k9_relat_1(B_793, A_794)) | ~v1_relat_1(B_793) | ~v2_funct_1(B_793) | ~v1_funct_1(B_793) | ~v1_relat_1(B_793))), inference(superposition, [status(thm), theory('equality')], [c_6971, c_34])).
% 21.05/12.66  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 21.05/12.66  tff(c_42, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 21.05/12.66  tff(c_118, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=A_39 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 21.05/12.66  tff(c_125, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_42, c_118])).
% 21.05/12.66  tff(c_22, plain, (![A_18]: (k10_relat_1(A_18, k2_relat_1(A_18))=k1_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 21.05/12.66  tff(c_593, plain, (![A_77, C_78, B_79]: (k3_xboole_0(A_77, k10_relat_1(C_78, B_79))=k10_relat_1(k7_relat_1(C_78, A_77), B_79) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_77])).
% 21.05/12.66  tff(c_2445, plain, (![A_149, A_150]: (k10_relat_1(k7_relat_1(A_149, A_150), k2_relat_1(A_149))=k3_xboole_0(A_150, k1_relat_1(A_149)) | ~v1_relat_1(A_149) | ~v1_relat_1(A_149))), inference(superposition, [status(thm), theory('equality')], [c_22, c_593])).
% 21.05/12.66  tff(c_20, plain, (![B_17, A_16]: (r1_tarski(k10_relat_1(B_17, A_16), k1_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 21.05/12.66  tff(c_6217, plain, (![A_235, A_236]: (r1_tarski(k3_xboole_0(A_235, k1_relat_1(A_236)), k1_relat_1(k7_relat_1(A_236, A_235))) | ~v1_relat_1(k7_relat_1(A_236, A_235)) | ~v1_relat_1(A_236) | ~v1_relat_1(A_236))), inference(superposition, [status(thm), theory('equality')], [c_2445, c_20])).
% 21.05/12.66  tff(c_6293, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_125, c_6217])).
% 21.05/12.66  tff(c_6325, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_6293])).
% 21.05/12.66  tff(c_6328, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_6325])).
% 21.05/12.66  tff(c_6331, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_6328])).
% 21.05/12.66  tff(c_6335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_6331])).
% 21.05/12.66  tff(c_6337, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_6325])).
% 21.05/12.66  tff(c_18, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 21.05/12.66  tff(c_389, plain, (![B_62, A_63]: (r1_tarski(k10_relat_1(B_62, A_63), k10_relat_1(B_62, k2_relat_1(B_62))) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_65])).
% 21.05/12.66  tff(c_4273, plain, (![B_193, A_194, A_195]: (r1_tarski(k10_relat_1(k7_relat_1(B_193, A_194), A_195), k10_relat_1(k7_relat_1(B_193, A_194), k9_relat_1(B_193, A_194))) | ~v1_relat_1(k7_relat_1(B_193, A_194)) | ~v1_relat_1(B_193))), inference(superposition, [status(thm), theory('equality')], [c_18, c_389])).
% 21.05/12.66  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.05/12.66  tff(c_413, plain, (![B_62, A_63]: (k10_relat_1(B_62, k2_relat_1(B_62))=k10_relat_1(B_62, A_63) | ~r1_tarski(k10_relat_1(B_62, k2_relat_1(B_62)), k10_relat_1(B_62, A_63)) | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_389, c_2])).
% 21.05/12.66  tff(c_4345, plain, (![B_193, A_194]: (k10_relat_1(k7_relat_1(B_193, A_194), k2_relat_1(k7_relat_1(B_193, A_194)))=k10_relat_1(k7_relat_1(B_193, A_194), k9_relat_1(B_193, A_194)) | ~v1_relat_1(k7_relat_1(B_193, A_194)) | ~v1_relat_1(B_193))), inference(resolution, [status(thm)], [c_4273, c_413])).
% 21.05/12.66  tff(c_24, plain, (![B_20, A_19]: (r1_tarski(k10_relat_1(B_20, A_19), k10_relat_1(B_20, k2_relat_1(B_20))) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 21.05/12.66  tff(c_9475, plain, (![A_293, A_294]: (r1_tarski(k3_xboole_0(A_293, k1_relat_1(A_294)), k10_relat_1(k7_relat_1(A_294, A_293), k2_relat_1(k7_relat_1(A_294, A_293)))) | ~v1_relat_1(k7_relat_1(A_294, A_293)) | ~v1_relat_1(A_294) | ~v1_relat_1(A_294))), inference(superposition, [status(thm), theory('equality')], [c_2445, c_24])).
% 21.05/12.66  tff(c_9607, plain, (r1_tarski('#skF_1', k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_125, c_9475])).
% 21.05/12.66  tff(c_9659, plain, (r1_tarski('#skF_1', k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_6337, c_9607])).
% 21.05/12.66  tff(c_9778, plain, (r1_tarski('#skF_1', k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4345, c_9659])).
% 21.05/12.66  tff(c_9807, plain, (r1_tarski('#skF_1', k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6337, c_9778])).
% 21.05/12.66  tff(c_62469, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_62279, c_9807])).
% 21.05/12.66  tff(c_62714, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_46, c_62469])).
% 21.05/12.66  tff(c_952, plain, (![B_96, A_97]: (k10_relat_1(B_96, k9_relat_1(B_96, A_97))=A_97 | ~r1_tarski(A_97, k10_relat_1(B_96, k9_relat_1(B_96, A_97))) | ~v2_funct_1(B_96) | ~v1_funct_1(B_96) | ~v1_relat_1(B_96))), inference(resolution, [status(thm)], [c_926, c_2])).
% 21.05/12.66  tff(c_62794, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_62714, c_952])).
% 21.05/12.66  tff(c_62844, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_62794])).
% 21.05/12.66  tff(c_62846, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_62844])).
% 21.05/12.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.05/12.66  
% 21.05/12.66  Inference rules
% 21.05/12.66  ----------------------
% 21.05/12.66  #Ref     : 0
% 21.05/12.66  #Sup     : 14857
% 21.05/12.66  #Fact    : 0
% 21.05/12.66  #Define  : 0
% 21.05/12.66  #Split   : 14
% 21.05/12.66  #Chain   : 0
% 21.05/12.66  #Close   : 0
% 21.05/12.66  
% 21.05/12.66  Ordering : KBO
% 21.05/12.66  
% 21.05/12.66  Simplification rules
% 21.05/12.66  ----------------------
% 21.05/12.66  #Subsume      : 3740
% 21.05/12.66  #Demod        : 13370
% 21.05/12.66  #Tautology    : 3390
% 21.05/12.66  #SimpNegUnit  : 2
% 21.05/12.66  #BackRed      : 12
% 21.05/12.66  
% 21.05/12.66  #Partial instantiations: 0
% 21.05/12.66  #Strategies tried      : 1
% 21.05/12.66  
% 21.05/12.66  Timing (in seconds)
% 21.05/12.66  ----------------------
% 21.05/12.66  Preprocessing        : 0.30
% 21.05/12.66  Parsing              : 0.16
% 21.05/12.66  CNF conversion       : 0.02
% 21.05/12.66  Main loop            : 11.59
% 21.05/12.66  Inferencing          : 1.71
% 21.05/12.66  Reduction            : 5.49
% 21.05/12.66  Demodulation         : 4.72
% 21.05/12.66  BG Simplification    : 0.21
% 21.05/12.66  Subsumption          : 3.67
% 21.05/12.66  Abstraction          : 0.35
% 21.05/12.66  MUC search           : 0.00
% 21.05/12.66  Cooper               : 0.00
% 21.05/12.66  Total                : 11.93
% 21.05/12.66  Index Insertion      : 0.00
% 21.05/12.66  Index Deletion       : 0.00
% 21.05/12.66  Index Matching       : 0.00
% 21.05/12.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
