%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:08 EST 2020

% Result     : Theorem 6.27s
% Output     : CNFRefutation 6.61s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 139 expanded)
%              Number of leaves         :   26 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  158 ( 353 expanded)
%              Number of equality atoms :   26 (  62 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_8 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( v3_ordinal1(B)
       => ~ ( r1_tarski(A,B)
            & A != k1_xboole_0
            & ! [C] :
                ( v3_ordinal1(C)
               => ~ ( r2_hidden(C,A)
                    & ! [D] :
                        ( v3_ordinal1(D)
                       => ( r2_hidden(D,A)
                         => r1_ordinal1(C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_ordinal1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_75,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_34,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_5'(A_13,B_14),B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    v3_ordinal1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_44,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_56,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_64,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_44,c_56])).

tff(c_98,plain,(
    ! [D_46,B_47,A_48] :
      ( r2_hidden(D_46,B_47)
      | ~ r2_hidden(D_46,k3_xboole_0(A_48,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_110,plain,(
    ! [D_49] :
      ( r2_hidden(D_49,'#skF_7')
      | ~ r2_hidden(D_49,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_98])).

tff(c_36,plain,(
    ! [A_20,B_21] :
      ( v3_ordinal1(A_20)
      | ~ r2_hidden(A_20,B_21)
      | ~ v3_ordinal1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_113,plain,(
    ! [D_49] :
      ( v3_ordinal1(D_49)
      | ~ v3_ordinal1('#skF_7')
      | ~ r2_hidden(D_49,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_110,c_36])).

tff(c_121,plain,(
    ! [D_50] :
      ( v3_ordinal1(D_50)
      | ~ r2_hidden(D_50,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_113])).

tff(c_126,plain,(
    ! [A_13] :
      ( v3_ordinal1('#skF_5'(A_13,'#skF_6'))
      | ~ r2_hidden(A_13,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_121])).

tff(c_1050,plain,(
    ! [A_130,B_131,C_132] :
      ( r2_hidden('#skF_1'(A_130,B_131,C_132),A_130)
      | r2_hidden('#skF_2'(A_130,B_131,C_132),C_132)
      | k3_xboole_0(A_130,B_131) = C_132 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1114,plain,(
    ! [A_130,B_131] :
      ( r2_hidden('#skF_2'(A_130,B_131,A_130),A_130)
      | k3_xboole_0(A_130,B_131) = A_130 ) ),
    inference(resolution,[status(thm)],[c_1050,c_14])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1620,plain,(
    ! [A_183,B_184,C_185] :
      ( r2_hidden('#skF_1'(A_183,B_184,C_185),B_184)
      | ~ r2_hidden('#skF_2'(A_183,B_184,C_185),B_184)
      | ~ r2_hidden('#skF_2'(A_183,B_184,C_185),A_183)
      | k3_xboole_0(A_183,B_184) = C_185 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3516,plain,(
    ! [C_354,B_355] :
      ( ~ r2_hidden('#skF_2'(C_354,B_355,C_354),B_355)
      | r2_hidden('#skF_1'(C_354,B_355,C_354),B_355)
      | k3_xboole_0(C_354,B_355) = C_354 ) ),
    inference(resolution,[status(thm)],[c_16,c_1620])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3570,plain,(
    ! [B_356] :
      ( ~ r2_hidden('#skF_2'(B_356,B_356,B_356),B_356)
      | k3_xboole_0(B_356,B_356) = B_356 ) ),
    inference(resolution,[status(thm)],[c_3516,c_8])).

tff(c_3603,plain,(
    ! [B_131] : k3_xboole_0(B_131,B_131) = B_131 ),
    inference(resolution,[status(thm)],[c_1114,c_3570])).

tff(c_52,plain,(
    ! [C_30] :
      ( v3_ordinal1('#skF_8'(C_30))
      | ~ r2_hidden(C_30,'#skF_6')
      | ~ v3_ordinal1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_50,plain,(
    ! [C_30] :
      ( r2_hidden('#skF_8'(C_30),'#skF_6')
      | ~ r2_hidden(C_30,'#skF_6')
      | ~ v3_ordinal1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_171,plain,(
    ! [B_63,A_64] :
      ( r2_hidden(B_63,A_64)
      | r1_ordinal1(A_64,B_63)
      | ~ v3_ordinal1(B_63)
      | ~ v3_ordinal1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2867,plain,(
    ! [B_270,B_271,A_272] :
      ( r2_hidden(B_270,B_271)
      | r1_ordinal1(k3_xboole_0(A_272,B_271),B_270)
      | ~ v3_ordinal1(B_270)
      | ~ v3_ordinal1(k3_xboole_0(A_272,B_271)) ) ),
    inference(resolution,[status(thm)],[c_171,c_4])).

tff(c_48,plain,(
    ! [C_30] :
      ( ~ r1_ordinal1(C_30,'#skF_8'(C_30))
      | ~ r2_hidden(C_30,'#skF_6')
      | ~ v3_ordinal1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3086,plain,(
    ! [A_302,B_303] :
      ( ~ r2_hidden(k3_xboole_0(A_302,B_303),'#skF_6')
      | r2_hidden('#skF_8'(k3_xboole_0(A_302,B_303)),B_303)
      | ~ v3_ordinal1('#skF_8'(k3_xboole_0(A_302,B_303)))
      | ~ v3_ordinal1(k3_xboole_0(A_302,B_303)) ) ),
    inference(resolution,[status(thm)],[c_2867,c_48])).

tff(c_32,plain,(
    ! [D_19,A_13,B_14] :
      ( ~ r2_hidden(D_19,'#skF_5'(A_13,B_14))
      | ~ r2_hidden(D_19,B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4997,plain,(
    ! [A_435,A_436,B_437] :
      ( ~ r2_hidden('#skF_8'(k3_xboole_0(A_435,'#skF_5'(A_436,B_437))),B_437)
      | ~ r2_hidden(A_436,B_437)
      | ~ r2_hidden(k3_xboole_0(A_435,'#skF_5'(A_436,B_437)),'#skF_6')
      | ~ v3_ordinal1('#skF_8'(k3_xboole_0(A_435,'#skF_5'(A_436,B_437))))
      | ~ v3_ordinal1(k3_xboole_0(A_435,'#skF_5'(A_436,B_437))) ) ),
    inference(resolution,[status(thm)],[c_3086,c_32])).

tff(c_5328,plain,(
    ! [A_461,A_462] :
      ( ~ r2_hidden(A_461,'#skF_6')
      | ~ v3_ordinal1('#skF_8'(k3_xboole_0(A_462,'#skF_5'(A_461,'#skF_6'))))
      | ~ r2_hidden(k3_xboole_0(A_462,'#skF_5'(A_461,'#skF_6')),'#skF_6')
      | ~ v3_ordinal1(k3_xboole_0(A_462,'#skF_5'(A_461,'#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_50,c_4997])).

tff(c_5927,plain,(
    ! [A_477,A_478] :
      ( ~ r2_hidden(A_477,'#skF_6')
      | ~ r2_hidden(k3_xboole_0(A_478,'#skF_5'(A_477,'#skF_6')),'#skF_6')
      | ~ v3_ordinal1(k3_xboole_0(A_478,'#skF_5'(A_477,'#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_52,c_5328])).

tff(c_5931,plain,(
    ! [A_477] :
      ( ~ r2_hidden(A_477,'#skF_6')
      | ~ r2_hidden('#skF_5'(A_477,'#skF_6'),'#skF_6')
      | ~ v3_ordinal1(k3_xboole_0('#skF_5'(A_477,'#skF_6'),'#skF_5'(A_477,'#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3603,c_5927])).

tff(c_5942,plain,(
    ! [A_479] :
      ( ~ r2_hidden(A_479,'#skF_6')
      | ~ r2_hidden('#skF_5'(A_479,'#skF_6'),'#skF_6')
      | ~ v3_ordinal1('#skF_5'(A_479,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3603,c_5931])).

tff(c_5952,plain,(
    ! [A_480] :
      ( ~ v3_ordinal1('#skF_5'(A_480,'#skF_6'))
      | ~ r2_hidden(A_480,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_5942])).

tff(c_5961,plain,(
    ! [A_13] : ~ r2_hidden(A_13,'#skF_6') ),
    inference(resolution,[status(thm)],[c_126,c_5952])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_280,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_3'(A_80,B_81),B_81)
      | r2_hidden('#skF_4'(A_80,B_81),A_80)
      | B_81 = A_80 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_77,plain,(
    ! [A_41,B_42] :
      ( r2_hidden('#skF_5'(A_41,B_42),B_42)
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    ! [B_26,A_25] :
      ( ~ r1_tarski(B_26,A_25)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_157,plain,(
    ! [B_57,A_58] :
      ( ~ r1_tarski(B_57,'#skF_5'(A_58,B_57))
      | ~ r2_hidden(A_58,B_57) ) ),
    inference(resolution,[status(thm)],[c_77,c_40])).

tff(c_162,plain,(
    ! [A_58] : ~ r2_hidden(A_58,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_157])).

tff(c_364,plain,(
    ! [A_83] :
      ( r2_hidden('#skF_4'(A_83,k1_xboole_0),A_83)
      | k1_xboole_0 = A_83 ) ),
    inference(resolution,[status(thm)],[c_280,c_162])).

tff(c_707,plain,(
    ! [A_97,B_98] :
      ( r2_hidden('#skF_4'(k3_xboole_0(A_97,B_98),k1_xboole_0),B_98)
      | k3_xboole_0(A_97,B_98) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_364,c_4])).

tff(c_745,plain,(
    ! [A_97] : k3_xboole_0(A_97,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_707,c_162])).

tff(c_800,plain,(
    ! [A_100,B_101,C_102] :
      ( r2_hidden('#skF_1'(A_100,B_101,C_102),B_101)
      | r2_hidden('#skF_2'(A_100,B_101,C_102),C_102)
      | k3_xboole_0(A_100,B_101) = C_102 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_808,plain,(
    ! [A_100,C_102] :
      ( r2_hidden('#skF_2'(A_100,k1_xboole_0,C_102),C_102)
      | k3_xboole_0(A_100,k1_xboole_0) = C_102 ) ),
    inference(resolution,[status(thm)],[c_800,c_162])).

tff(c_879,plain,(
    ! [A_103,C_104] :
      ( r2_hidden('#skF_2'(A_103,k1_xboole_0,C_104),C_104)
      | k1_xboole_0 = C_104 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_808])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2777,plain,(
    ! [A_266,A_267,B_268] :
      ( r2_hidden('#skF_2'(A_266,k1_xboole_0,k3_xboole_0(A_267,B_268)),A_267)
      | k3_xboole_0(A_267,B_268) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_879,c_6])).

tff(c_2819,plain,(
    ! [A_266] :
      ( r2_hidden('#skF_2'(A_266,k1_xboole_0,'#skF_6'),'#skF_6')
      | k3_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2777])).

tff(c_2838,plain,(
    ! [A_266] :
      ( r2_hidden('#skF_2'(A_266,k1_xboole_0,'#skF_6'),'#skF_6')
      | k1_xboole_0 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2819])).

tff(c_2839,plain,(
    ! [A_266] : r2_hidden('#skF_2'(A_266,k1_xboole_0,'#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2838])).

tff(c_5967,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5961,c_2839])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % DateTime   : Tue Dec  1 11:31:20 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.27/2.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.27/2.30  
% 6.27/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.27/2.30  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_8 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4
% 6.27/2.30  
% 6.27/2.30  %Foreground sorts:
% 6.27/2.30  
% 6.27/2.30  
% 6.27/2.30  %Background operators:
% 6.27/2.30  
% 6.27/2.30  
% 6.27/2.30  %Foreground operators:
% 6.27/2.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.27/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.27/2.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.27/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.27/2.30  tff('#skF_8', type, '#skF_8': $i > $i).
% 6.27/2.30  tff('#skF_7', type, '#skF_7': $i).
% 6.27/2.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.27/2.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.27/2.30  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 6.27/2.30  tff('#skF_6', type, '#skF_6': $i).
% 6.27/2.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.27/2.30  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 6.27/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.27/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.27/2.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.27/2.30  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.27/2.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.27/2.30  
% 6.61/2.32  tff(f_60, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 6.61/2.32  tff(f_102, negated_conjecture, ~(![A, B]: (v3_ordinal1(B) => ~((r1_tarski(A, B) & ~(A = k1_xboole_0)) & (![C]: (v3_ordinal1(C) => ~(r2_hidden(C, A) & (![D]: (v3_ordinal1(D) => (r2_hidden(D, A) => r1_ordinal1(C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_ordinal1)).
% 6.61/2.32  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.61/2.32  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 6.61/2.32  tff(f_66, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 6.61/2.32  tff(f_75, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 6.61/2.32  tff(f_41, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 6.61/2.32  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.61/2.32  tff(f_80, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.61/2.32  tff(c_34, plain, (![A_13, B_14]: (r2_hidden('#skF_5'(A_13, B_14), B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.61/2.32  tff(c_46, plain, (v3_ordinal1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.61/2.32  tff(c_44, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.61/2.32  tff(c_56, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=A_37 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.61/2.32  tff(c_64, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_44, c_56])).
% 6.61/2.32  tff(c_98, plain, (![D_46, B_47, A_48]: (r2_hidden(D_46, B_47) | ~r2_hidden(D_46, k3_xboole_0(A_48, B_47)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.61/2.32  tff(c_110, plain, (![D_49]: (r2_hidden(D_49, '#skF_7') | ~r2_hidden(D_49, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_98])).
% 6.61/2.32  tff(c_36, plain, (![A_20, B_21]: (v3_ordinal1(A_20) | ~r2_hidden(A_20, B_21) | ~v3_ordinal1(B_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.61/2.32  tff(c_113, plain, (![D_49]: (v3_ordinal1(D_49) | ~v3_ordinal1('#skF_7') | ~r2_hidden(D_49, '#skF_6'))), inference(resolution, [status(thm)], [c_110, c_36])).
% 6.61/2.32  tff(c_121, plain, (![D_50]: (v3_ordinal1(D_50) | ~r2_hidden(D_50, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_113])).
% 6.61/2.32  tff(c_126, plain, (![A_13]: (v3_ordinal1('#skF_5'(A_13, '#skF_6')) | ~r2_hidden(A_13, '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_121])).
% 6.61/2.32  tff(c_1050, plain, (![A_130, B_131, C_132]: (r2_hidden('#skF_1'(A_130, B_131, C_132), A_130) | r2_hidden('#skF_2'(A_130, B_131, C_132), C_132) | k3_xboole_0(A_130, B_131)=C_132)), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.61/2.32  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.61/2.32  tff(c_1114, plain, (![A_130, B_131]: (r2_hidden('#skF_2'(A_130, B_131, A_130), A_130) | k3_xboole_0(A_130, B_131)=A_130)), inference(resolution, [status(thm)], [c_1050, c_14])).
% 6.61/2.32  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.61/2.32  tff(c_1620, plain, (![A_183, B_184, C_185]: (r2_hidden('#skF_1'(A_183, B_184, C_185), B_184) | ~r2_hidden('#skF_2'(A_183, B_184, C_185), B_184) | ~r2_hidden('#skF_2'(A_183, B_184, C_185), A_183) | k3_xboole_0(A_183, B_184)=C_185)), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.61/2.32  tff(c_3516, plain, (![C_354, B_355]: (~r2_hidden('#skF_2'(C_354, B_355, C_354), B_355) | r2_hidden('#skF_1'(C_354, B_355, C_354), B_355) | k3_xboole_0(C_354, B_355)=C_354)), inference(resolution, [status(thm)], [c_16, c_1620])).
% 6.61/2.32  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.61/2.32  tff(c_3570, plain, (![B_356]: (~r2_hidden('#skF_2'(B_356, B_356, B_356), B_356) | k3_xboole_0(B_356, B_356)=B_356)), inference(resolution, [status(thm)], [c_3516, c_8])).
% 6.61/2.32  tff(c_3603, plain, (![B_131]: (k3_xboole_0(B_131, B_131)=B_131)), inference(resolution, [status(thm)], [c_1114, c_3570])).
% 6.61/2.32  tff(c_52, plain, (![C_30]: (v3_ordinal1('#skF_8'(C_30)) | ~r2_hidden(C_30, '#skF_6') | ~v3_ordinal1(C_30))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.61/2.32  tff(c_50, plain, (![C_30]: (r2_hidden('#skF_8'(C_30), '#skF_6') | ~r2_hidden(C_30, '#skF_6') | ~v3_ordinal1(C_30))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.61/2.32  tff(c_171, plain, (![B_63, A_64]: (r2_hidden(B_63, A_64) | r1_ordinal1(A_64, B_63) | ~v3_ordinal1(B_63) | ~v3_ordinal1(A_64))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.61/2.32  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.61/2.32  tff(c_2867, plain, (![B_270, B_271, A_272]: (r2_hidden(B_270, B_271) | r1_ordinal1(k3_xboole_0(A_272, B_271), B_270) | ~v3_ordinal1(B_270) | ~v3_ordinal1(k3_xboole_0(A_272, B_271)))), inference(resolution, [status(thm)], [c_171, c_4])).
% 6.61/2.32  tff(c_48, plain, (![C_30]: (~r1_ordinal1(C_30, '#skF_8'(C_30)) | ~r2_hidden(C_30, '#skF_6') | ~v3_ordinal1(C_30))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.61/2.32  tff(c_3086, plain, (![A_302, B_303]: (~r2_hidden(k3_xboole_0(A_302, B_303), '#skF_6') | r2_hidden('#skF_8'(k3_xboole_0(A_302, B_303)), B_303) | ~v3_ordinal1('#skF_8'(k3_xboole_0(A_302, B_303))) | ~v3_ordinal1(k3_xboole_0(A_302, B_303)))), inference(resolution, [status(thm)], [c_2867, c_48])).
% 6.61/2.32  tff(c_32, plain, (![D_19, A_13, B_14]: (~r2_hidden(D_19, '#skF_5'(A_13, B_14)) | ~r2_hidden(D_19, B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.61/2.32  tff(c_4997, plain, (![A_435, A_436, B_437]: (~r2_hidden('#skF_8'(k3_xboole_0(A_435, '#skF_5'(A_436, B_437))), B_437) | ~r2_hidden(A_436, B_437) | ~r2_hidden(k3_xboole_0(A_435, '#skF_5'(A_436, B_437)), '#skF_6') | ~v3_ordinal1('#skF_8'(k3_xboole_0(A_435, '#skF_5'(A_436, B_437)))) | ~v3_ordinal1(k3_xboole_0(A_435, '#skF_5'(A_436, B_437))))), inference(resolution, [status(thm)], [c_3086, c_32])).
% 6.61/2.32  tff(c_5328, plain, (![A_461, A_462]: (~r2_hidden(A_461, '#skF_6') | ~v3_ordinal1('#skF_8'(k3_xboole_0(A_462, '#skF_5'(A_461, '#skF_6')))) | ~r2_hidden(k3_xboole_0(A_462, '#skF_5'(A_461, '#skF_6')), '#skF_6') | ~v3_ordinal1(k3_xboole_0(A_462, '#skF_5'(A_461, '#skF_6'))))), inference(resolution, [status(thm)], [c_50, c_4997])).
% 6.61/2.32  tff(c_5927, plain, (![A_477, A_478]: (~r2_hidden(A_477, '#skF_6') | ~r2_hidden(k3_xboole_0(A_478, '#skF_5'(A_477, '#skF_6')), '#skF_6') | ~v3_ordinal1(k3_xboole_0(A_478, '#skF_5'(A_477, '#skF_6'))))), inference(resolution, [status(thm)], [c_52, c_5328])).
% 6.61/2.32  tff(c_5931, plain, (![A_477]: (~r2_hidden(A_477, '#skF_6') | ~r2_hidden('#skF_5'(A_477, '#skF_6'), '#skF_6') | ~v3_ordinal1(k3_xboole_0('#skF_5'(A_477, '#skF_6'), '#skF_5'(A_477, '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_3603, c_5927])).
% 6.61/2.32  tff(c_5942, plain, (![A_479]: (~r2_hidden(A_479, '#skF_6') | ~r2_hidden('#skF_5'(A_479, '#skF_6'), '#skF_6') | ~v3_ordinal1('#skF_5'(A_479, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_3603, c_5931])).
% 6.61/2.32  tff(c_5952, plain, (![A_480]: (~v3_ordinal1('#skF_5'(A_480, '#skF_6')) | ~r2_hidden(A_480, '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_5942])).
% 6.61/2.32  tff(c_5961, plain, (![A_13]: (~r2_hidden(A_13, '#skF_6'))), inference(resolution, [status(thm)], [c_126, c_5952])).
% 6.61/2.32  tff(c_42, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.61/2.32  tff(c_280, plain, (![A_80, B_81]: (r2_hidden('#skF_3'(A_80, B_81), B_81) | r2_hidden('#skF_4'(A_80, B_81), A_80) | B_81=A_80)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.61/2.32  tff(c_30, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.61/2.32  tff(c_77, plain, (![A_41, B_42]: (r2_hidden('#skF_5'(A_41, B_42), B_42) | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.61/2.32  tff(c_40, plain, (![B_26, A_25]: (~r1_tarski(B_26, A_25) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.61/2.32  tff(c_157, plain, (![B_57, A_58]: (~r1_tarski(B_57, '#skF_5'(A_58, B_57)) | ~r2_hidden(A_58, B_57))), inference(resolution, [status(thm)], [c_77, c_40])).
% 6.61/2.32  tff(c_162, plain, (![A_58]: (~r2_hidden(A_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_157])).
% 6.61/2.32  tff(c_364, plain, (![A_83]: (r2_hidden('#skF_4'(A_83, k1_xboole_0), A_83) | k1_xboole_0=A_83)), inference(resolution, [status(thm)], [c_280, c_162])).
% 6.61/2.32  tff(c_707, plain, (![A_97, B_98]: (r2_hidden('#skF_4'(k3_xboole_0(A_97, B_98), k1_xboole_0), B_98) | k3_xboole_0(A_97, B_98)=k1_xboole_0)), inference(resolution, [status(thm)], [c_364, c_4])).
% 6.61/2.32  tff(c_745, plain, (![A_97]: (k3_xboole_0(A_97, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_707, c_162])).
% 6.61/2.32  tff(c_800, plain, (![A_100, B_101, C_102]: (r2_hidden('#skF_1'(A_100, B_101, C_102), B_101) | r2_hidden('#skF_2'(A_100, B_101, C_102), C_102) | k3_xboole_0(A_100, B_101)=C_102)), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.61/2.32  tff(c_808, plain, (![A_100, C_102]: (r2_hidden('#skF_2'(A_100, k1_xboole_0, C_102), C_102) | k3_xboole_0(A_100, k1_xboole_0)=C_102)), inference(resolution, [status(thm)], [c_800, c_162])).
% 6.61/2.32  tff(c_879, plain, (![A_103, C_104]: (r2_hidden('#skF_2'(A_103, k1_xboole_0, C_104), C_104) | k1_xboole_0=C_104)), inference(demodulation, [status(thm), theory('equality')], [c_745, c_808])).
% 6.61/2.32  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.61/2.32  tff(c_2777, plain, (![A_266, A_267, B_268]: (r2_hidden('#skF_2'(A_266, k1_xboole_0, k3_xboole_0(A_267, B_268)), A_267) | k3_xboole_0(A_267, B_268)=k1_xboole_0)), inference(resolution, [status(thm)], [c_879, c_6])).
% 6.61/2.32  tff(c_2819, plain, (![A_266]: (r2_hidden('#skF_2'(A_266, k1_xboole_0, '#skF_6'), '#skF_6') | k3_xboole_0('#skF_6', '#skF_7')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_64, c_2777])).
% 6.61/2.32  tff(c_2838, plain, (![A_266]: (r2_hidden('#skF_2'(A_266, k1_xboole_0, '#skF_6'), '#skF_6') | k1_xboole_0='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2819])).
% 6.61/2.32  tff(c_2839, plain, (![A_266]: (r2_hidden('#skF_2'(A_266, k1_xboole_0, '#skF_6'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_42, c_2838])).
% 6.61/2.32  tff(c_5967, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5961, c_2839])).
% 6.61/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.61/2.32  
% 6.61/2.32  Inference rules
% 6.61/2.32  ----------------------
% 6.61/2.32  #Ref     : 0
% 6.61/2.32  #Sup     : 1166
% 6.61/2.32  #Fact    : 0
% 6.61/2.32  #Define  : 0
% 6.61/2.32  #Split   : 6
% 6.61/2.32  #Chain   : 0
% 6.61/2.32  #Close   : 0
% 6.61/2.32  
% 6.61/2.32  Ordering : KBO
% 6.61/2.32  
% 6.61/2.32  Simplification rules
% 6.61/2.32  ----------------------
% 6.61/2.32  #Subsume      : 472
% 6.61/2.32  #Demod        : 980
% 6.61/2.32  #Tautology    : 277
% 6.61/2.32  #SimpNegUnit  : 168
% 6.61/2.32  #BackRed      : 13
% 6.61/2.32  
% 6.61/2.32  #Partial instantiations: 0
% 6.61/2.32  #Strategies tried      : 1
% 6.61/2.32  
% 6.61/2.32  Timing (in seconds)
% 6.61/2.32  ----------------------
% 6.61/2.32  Preprocessing        : 0.31
% 6.61/2.32  Parsing              : 0.16
% 6.61/2.32  CNF conversion       : 0.02
% 6.61/2.32  Main loop            : 1.21
% 6.61/2.32  Inferencing          : 0.46
% 6.61/2.32  Reduction            : 0.37
% 6.61/2.32  Demodulation         : 0.24
% 6.61/2.32  BG Simplification    : 0.04
% 6.61/2.32  Subsumption          : 0.25
% 6.61/2.32  Abstraction          : 0.05
% 6.61/2.32  MUC search           : 0.00
% 6.61/2.32  Cooper               : 0.00
% 6.61/2.32  Total                : 1.55
% 6.61/2.32  Index Insertion      : 0.00
% 6.61/2.32  Index Deletion       : 0.00
% 6.61/2.32  Index Matching       : 0.00
% 6.61/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
