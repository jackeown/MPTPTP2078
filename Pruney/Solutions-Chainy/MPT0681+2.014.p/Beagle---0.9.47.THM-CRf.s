%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:27 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 174 expanded)
%              Number of leaves         :   33 (  75 expanded)
%              Depth                    :   17
%              Number of atoms          :  119 ( 316 expanded)
%              Number of equality atoms :   33 (  82 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_43,axiom,(
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

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

tff(c_34,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_14,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_80,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_xboole_0(A_34,B_35)
      | ~ r2_hidden(C_36,k3_xboole_0(A_34,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_83,plain,(
    ! [A_11,C_36] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_36,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_80])).

tff(c_85,plain,(
    ! [C_36] : ~ r2_hidden(C_36,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_83])).

tff(c_42,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_28,plain,(
    ! [A_22] : v1_relat_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_122,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_1'(A_42,B_43),A_42)
      | r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_131,plain,(
    ! [B_43] : r1_xboole_0(k1_xboole_0,B_43) ),
    inference(resolution,[status(thm)],[c_122,c_85])).

tff(c_208,plain,(
    ! [A_61,B_62] :
      ( k7_relat_1(A_61,B_62) = k1_xboole_0
      | ~ r1_xboole_0(B_62,k1_relat_1(A_61))
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_261,plain,(
    ! [A_66] :
      ( k7_relat_1(A_66,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_66) ) ),
    inference(resolution,[status(thm)],[c_131,c_208])).

tff(c_279,plain,(
    ! [A_67] : k7_relat_1(k6_relat_1(A_67),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_261])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( k2_relat_1(k7_relat_1(B_17,A_16)) = k9_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_284,plain,(
    ! [A_67] :
      ( k9_relat_1(k6_relat_1(A_67),k1_xboole_0) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k6_relat_1(A_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_20])).

tff(c_305,plain,(
    ! [A_68] : k9_relat_1(k6_relat_1(A_68),k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_284])).

tff(c_26,plain,(
    ! [A_21] : k2_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_99,plain,(
    ! [A_40] :
      ( k9_relat_1(A_40,k1_relat_1(A_40)) = k2_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_108,plain,(
    ! [A_21] :
      ( k9_relat_1(k6_relat_1(A_21),A_21) = k2_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_99])).

tff(c_112,plain,(
    ! [A_21] : k9_relat_1(k6_relat_1(A_21),A_21) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_108])).

tff(c_317,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_112])).

tff(c_269,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_261])).

tff(c_273,plain,
    ( k9_relat_1('#skF_5',k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_20])).

tff(c_277,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_273])).

tff(c_358,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_277])).

tff(c_38,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_87,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_1'(A_38,B_39),B_39)
      | r1_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_98,plain,(
    ! [A_6,B_7,A_38] :
      ( ~ r1_xboole_0(A_6,B_7)
      | r1_xboole_0(A_38,k3_xboole_0(A_6,B_7)) ) ),
    inference(resolution,[status(thm)],[c_87,c_10])).

tff(c_219,plain,(
    ! [A_21,B_62] :
      ( k7_relat_1(k6_relat_1(A_21),B_62) = k1_xboole_0
      | ~ r1_xboole_0(B_62,A_21)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_208])).

tff(c_330,plain,(
    ! [A_69,B_70] :
      ( k7_relat_1(k6_relat_1(A_69),B_70) = k1_xboole_0
      | ~ r1_xboole_0(B_70,A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_219])).

tff(c_340,plain,(
    ! [A_69,B_70] :
      ( k9_relat_1(k6_relat_1(A_69),B_70) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k6_relat_1(A_69))
      | ~ r1_xboole_0(B_70,A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_20])).

tff(c_352,plain,(
    ! [A_69,B_70] :
      ( k9_relat_1(k6_relat_1(A_69),B_70) = k2_relat_1(k1_xboole_0)
      | ~ r1_xboole_0(B_70,A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_340])).

tff(c_407,plain,(
    ! [A_72,B_73] :
      ( k9_relat_1(k6_relat_1(A_72),B_73) = k1_xboole_0
      | ~ r1_xboole_0(B_73,A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_352])).

tff(c_458,plain,(
    ! [B_74] :
      ( k1_xboole_0 = B_74
      | ~ r1_xboole_0(B_74,B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_112])).

tff(c_533,plain,(
    ! [A_81,B_82] :
      ( k3_xboole_0(A_81,B_82) = k1_xboole_0
      | ~ r1_xboole_0(A_81,B_82) ) ),
    inference(resolution,[status(thm)],[c_98,c_458])).

tff(c_558,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_533])).

tff(c_224,plain,(
    ! [C_63,A_64,B_65] :
      ( k3_xboole_0(k9_relat_1(C_63,A_64),k9_relat_1(C_63,B_65)) = k9_relat_1(C_63,k3_xboole_0(A_64,B_65))
      | ~ v2_funct_1(C_63)
      | ~ v1_funct_1(C_63)
      | ~ v1_relat_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),k3_xboole_0(A_6,B_7))
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1499,plain,(
    ! [C_111,A_112,B_113] :
      ( r2_hidden('#skF_2'(k9_relat_1(C_111,A_112),k9_relat_1(C_111,B_113)),k9_relat_1(C_111,k3_xboole_0(A_112,B_113)))
      | r1_xboole_0(k9_relat_1(C_111,A_112),k9_relat_1(C_111,B_113))
      | ~ v2_funct_1(C_111)
      | ~ v1_funct_1(C_111)
      | ~ v1_relat_1(C_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_8])).

tff(c_1771,plain,(
    ! [C_120] :
      ( r2_hidden('#skF_2'(k9_relat_1(C_120,'#skF_3'),k9_relat_1(C_120,'#skF_4')),k9_relat_1(C_120,k1_xboole_0))
      | r1_xboole_0(k9_relat_1(C_120,'#skF_3'),k9_relat_1(C_120,'#skF_4'))
      | ~ v2_funct_1(C_120)
      | ~ v1_funct_1(C_120)
      | ~ v1_relat_1(C_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_1499])).

tff(c_1789,plain,
    ( r2_hidden('#skF_2'(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4')),k1_xboole_0)
    | r1_xboole_0(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_1771])).

tff(c_1815,plain,
    ( r2_hidden('#skF_2'(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4')),k1_xboole_0)
    | r1_xboole_0(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_1789])).

tff(c_1817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_85,c_1815])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:55:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.62  
% 3.47/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.62  %$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.47/1.62  
% 3.47/1.62  %Foreground sorts:
% 3.47/1.62  
% 3.47/1.62  
% 3.47/1.62  %Background operators:
% 3.47/1.62  
% 3.47/1.62  
% 3.47/1.62  %Foreground operators:
% 3.47/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.47/1.62  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.47/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.47/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.47/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.47/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.47/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.47/1.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.47/1.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.47/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.47/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.62  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.47/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.47/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.47/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.47/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.47/1.62  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.47/1.62  
% 3.47/1.65  tff(f_105, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_funct_1)).
% 3.47/1.65  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.47/1.65  tff(f_59, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.47/1.65  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.47/1.65  tff(f_86, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.47/1.65  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.47/1.65  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 3.47/1.65  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.47/1.65  tff(f_82, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.47/1.65  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.47/1.65  tff(f_94, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 3.47/1.65  tff(c_34, plain, (~r1_xboole_0(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.47/1.65  tff(c_14, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.47/1.65  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.47/1.65  tff(c_80, plain, (![A_34, B_35, C_36]: (~r1_xboole_0(A_34, B_35) | ~r2_hidden(C_36, k3_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.47/1.65  tff(c_83, plain, (![A_11, C_36]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_36, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_80])).
% 3.47/1.65  tff(c_85, plain, (![C_36]: (~r2_hidden(C_36, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_83])).
% 3.47/1.65  tff(c_42, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.47/1.65  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.47/1.65  tff(c_36, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.47/1.65  tff(c_28, plain, (![A_22]: (v1_relat_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.47/1.65  tff(c_122, plain, (![A_42, B_43]: (r2_hidden('#skF_1'(A_42, B_43), A_42) | r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.47/1.65  tff(c_131, plain, (![B_43]: (r1_xboole_0(k1_xboole_0, B_43))), inference(resolution, [status(thm)], [c_122, c_85])).
% 3.47/1.65  tff(c_208, plain, (![A_61, B_62]: (k7_relat_1(A_61, B_62)=k1_xboole_0 | ~r1_xboole_0(B_62, k1_relat_1(A_61)) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.47/1.65  tff(c_261, plain, (![A_66]: (k7_relat_1(A_66, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_66))), inference(resolution, [status(thm)], [c_131, c_208])).
% 3.47/1.65  tff(c_279, plain, (![A_67]: (k7_relat_1(k6_relat_1(A_67), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_261])).
% 3.47/1.65  tff(c_20, plain, (![B_17, A_16]: (k2_relat_1(k7_relat_1(B_17, A_16))=k9_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.47/1.65  tff(c_284, plain, (![A_67]: (k9_relat_1(k6_relat_1(A_67), k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k6_relat_1(A_67)))), inference(superposition, [status(thm), theory('equality')], [c_279, c_20])).
% 3.47/1.65  tff(c_305, plain, (![A_68]: (k9_relat_1(k6_relat_1(A_68), k1_xboole_0)=k2_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_284])).
% 3.47/1.65  tff(c_26, plain, (![A_21]: (k2_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.47/1.65  tff(c_24, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.47/1.65  tff(c_99, plain, (![A_40]: (k9_relat_1(A_40, k1_relat_1(A_40))=k2_relat_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.47/1.65  tff(c_108, plain, (![A_21]: (k9_relat_1(k6_relat_1(A_21), A_21)=k2_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_99])).
% 3.47/1.65  tff(c_112, plain, (![A_21]: (k9_relat_1(k6_relat_1(A_21), A_21)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_108])).
% 3.47/1.65  tff(c_317, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_305, c_112])).
% 3.47/1.65  tff(c_269, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_261])).
% 3.47/1.65  tff(c_273, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_269, c_20])).
% 3.47/1.65  tff(c_277, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k2_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_273])).
% 3.47/1.65  tff(c_358, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_317, c_277])).
% 3.47/1.65  tff(c_38, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.47/1.65  tff(c_87, plain, (![A_38, B_39]: (r2_hidden('#skF_1'(A_38, B_39), B_39) | r1_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.47/1.65  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.47/1.65  tff(c_98, plain, (![A_6, B_7, A_38]: (~r1_xboole_0(A_6, B_7) | r1_xboole_0(A_38, k3_xboole_0(A_6, B_7)))), inference(resolution, [status(thm)], [c_87, c_10])).
% 3.47/1.65  tff(c_219, plain, (![A_21, B_62]: (k7_relat_1(k6_relat_1(A_21), B_62)=k1_xboole_0 | ~r1_xboole_0(B_62, A_21) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_208])).
% 3.47/1.65  tff(c_330, plain, (![A_69, B_70]: (k7_relat_1(k6_relat_1(A_69), B_70)=k1_xboole_0 | ~r1_xboole_0(B_70, A_69))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_219])).
% 3.47/1.65  tff(c_340, plain, (![A_69, B_70]: (k9_relat_1(k6_relat_1(A_69), B_70)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k6_relat_1(A_69)) | ~r1_xboole_0(B_70, A_69))), inference(superposition, [status(thm), theory('equality')], [c_330, c_20])).
% 3.47/1.65  tff(c_352, plain, (![A_69, B_70]: (k9_relat_1(k6_relat_1(A_69), B_70)=k2_relat_1(k1_xboole_0) | ~r1_xboole_0(B_70, A_69))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_340])).
% 3.47/1.65  tff(c_407, plain, (![A_72, B_73]: (k9_relat_1(k6_relat_1(A_72), B_73)=k1_xboole_0 | ~r1_xboole_0(B_73, A_72))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_352])).
% 3.47/1.65  tff(c_458, plain, (![B_74]: (k1_xboole_0=B_74 | ~r1_xboole_0(B_74, B_74))), inference(superposition, [status(thm), theory('equality')], [c_407, c_112])).
% 3.47/1.65  tff(c_533, plain, (![A_81, B_82]: (k3_xboole_0(A_81, B_82)=k1_xboole_0 | ~r1_xboole_0(A_81, B_82))), inference(resolution, [status(thm)], [c_98, c_458])).
% 3.47/1.65  tff(c_558, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_533])).
% 3.47/1.65  tff(c_224, plain, (![C_63, A_64, B_65]: (k3_xboole_0(k9_relat_1(C_63, A_64), k9_relat_1(C_63, B_65))=k9_relat_1(C_63, k3_xboole_0(A_64, B_65)) | ~v2_funct_1(C_63) | ~v1_funct_1(C_63) | ~v1_relat_1(C_63))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.47/1.65  tff(c_8, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), k3_xboole_0(A_6, B_7)) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.47/1.65  tff(c_1499, plain, (![C_111, A_112, B_113]: (r2_hidden('#skF_2'(k9_relat_1(C_111, A_112), k9_relat_1(C_111, B_113)), k9_relat_1(C_111, k3_xboole_0(A_112, B_113))) | r1_xboole_0(k9_relat_1(C_111, A_112), k9_relat_1(C_111, B_113)) | ~v2_funct_1(C_111) | ~v1_funct_1(C_111) | ~v1_relat_1(C_111))), inference(superposition, [status(thm), theory('equality')], [c_224, c_8])).
% 3.47/1.65  tff(c_1771, plain, (![C_120]: (r2_hidden('#skF_2'(k9_relat_1(C_120, '#skF_3'), k9_relat_1(C_120, '#skF_4')), k9_relat_1(C_120, k1_xboole_0)) | r1_xboole_0(k9_relat_1(C_120, '#skF_3'), k9_relat_1(C_120, '#skF_4')) | ~v2_funct_1(C_120) | ~v1_funct_1(C_120) | ~v1_relat_1(C_120))), inference(superposition, [status(thm), theory('equality')], [c_558, c_1499])).
% 3.47/1.65  tff(c_1789, plain, (r2_hidden('#skF_2'(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4')), k1_xboole_0) | r1_xboole_0(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_358, c_1771])).
% 3.47/1.65  tff(c_1815, plain, (r2_hidden('#skF_2'(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4')), k1_xboole_0) | r1_xboole_0(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_1789])).
% 3.47/1.65  tff(c_1817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_85, c_1815])).
% 3.47/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.65  
% 3.47/1.65  Inference rules
% 3.47/1.65  ----------------------
% 3.47/1.65  #Ref     : 0
% 3.47/1.65  #Sup     : 399
% 3.47/1.65  #Fact    : 0
% 3.47/1.65  #Define  : 0
% 3.47/1.65  #Split   : 0
% 3.47/1.65  #Chain   : 0
% 3.47/1.65  #Close   : 0
% 3.47/1.65  
% 3.47/1.65  Ordering : KBO
% 3.47/1.65  
% 3.47/1.65  Simplification rules
% 3.47/1.65  ----------------------
% 3.47/1.65  #Subsume      : 59
% 3.47/1.65  #Demod        : 455
% 3.47/1.65  #Tautology    : 182
% 3.47/1.65  #SimpNegUnit  : 20
% 3.47/1.65  #BackRed      : 3
% 3.47/1.65  
% 3.47/1.65  #Partial instantiations: 0
% 3.47/1.65  #Strategies tried      : 1
% 3.47/1.65  
% 3.47/1.65  Timing (in seconds)
% 3.47/1.65  ----------------------
% 3.79/1.65  Preprocessing        : 0.29
% 3.79/1.65  Parsing              : 0.16
% 3.79/1.65  CNF conversion       : 0.02
% 3.79/1.65  Main loop            : 0.54
% 3.79/1.65  Inferencing          : 0.19
% 3.79/1.65  Reduction            : 0.20
% 3.79/1.65  Demodulation         : 0.15
% 3.79/1.65  BG Simplification    : 0.02
% 3.79/1.65  Subsumption          : 0.09
% 3.79/1.65  Abstraction          : 0.03
% 3.79/1.65  MUC search           : 0.00
% 3.79/1.65  Cooper               : 0.00
% 3.79/1.65  Total                : 0.89
% 3.79/1.65  Index Insertion      : 0.00
% 3.79/1.65  Index Deletion       : 0.00
% 3.79/1.65  Index Matching       : 0.00
% 3.79/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
