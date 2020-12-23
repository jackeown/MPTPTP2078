%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:40 EST 2020

% Result     : Theorem 11.60s
% Output     : CNFRefutation 11.75s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 115 expanded)
%              Number of leaves         :   32 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  116 ( 195 expanded)
%              Number of equality atoms :   27 (  52 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_47,axiom,(
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

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_55,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_50,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_5'),'#skF_4')
    | k10_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_99,plain,(
    k10_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_48,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_144,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_170,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_144])).

tff(c_174,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_170])).

tff(c_56,plain,
    ( k10_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_255,plain,(
    r1_xboole_0(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_56])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_261,plain,(
    k4_xboole_0(k2_relat_1('#skF_5'),'#skF_4') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_255,c_18])).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_297,plain,(
    k4_xboole_0(k2_relat_1('#skF_5'),k2_relat_1('#skF_5')) = k3_xboole_0(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_14])).

tff(c_300,plain,(
    k3_xboole_0(k2_relat_1('#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_297])).

tff(c_376,plain,(
    ! [B_70,A_71] :
      ( k10_relat_1(B_70,k3_xboole_0(k2_relat_1(B_70),A_71)) = k10_relat_1(B_70,A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_385,plain,
    ( k10_relat_1('#skF_5',k1_xboole_0) = k10_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_376])).

tff(c_397,plain,(
    k10_relat_1('#skF_5',k1_xboole_0) = k10_relat_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_385])).

tff(c_535,plain,(
    ! [A_97,B_98,C_99] :
      ( r2_hidden('#skF_3'(A_97,B_98,C_99),B_98)
      | ~ r2_hidden(A_97,k10_relat_1(C_99,B_98))
      | ~ v1_relat_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_16,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_78,plain,(
    ! [A_40,B_41] :
      ( ~ r2_hidden(A_40,B_41)
      | ~ r1_xboole_0(k1_tarski(A_40),B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_83,plain,(
    ! [A_40] : ~ r2_hidden(A_40,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_78])).

tff(c_911,plain,(
    ! [A_119,C_120] :
      ( ~ r2_hidden(A_119,k10_relat_1(C_120,k1_xboole_0))
      | ~ v1_relat_1(C_120) ) ),
    inference(resolution,[status(thm)],[c_535,c_83])).

tff(c_922,plain,(
    ! [A_119] :
      ( ~ r2_hidden(A_119,k10_relat_1('#skF_5','#skF_4'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_911])).

tff(c_959,plain,(
    ! [A_124] : ~ r2_hidden(A_124,k10_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_922])).

tff(c_980,plain,(
    ! [A_125] : r1_xboole_0(A_125,k10_relat_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_959])).

tff(c_1010,plain,(
    ! [A_129] : k4_xboole_0(A_129,k10_relat_1('#skF_5','#skF_4')) = A_129 ),
    inference(resolution,[status(thm)],[c_980,c_18])).

tff(c_1029,plain,(
    k10_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1010,c_174])).

tff(c_1053,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_1029])).

tff(c_1054,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,(
    ! [A_23] :
      ( k9_relat_1(A_23,k1_relat_1(A_23)) = k2_relat_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1055,plain,(
    k10_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_28,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden(k4_tarski('#skF_2'(A_17,B_18,C_19),A_17),C_19)
      | ~ r2_hidden(A_17,k9_relat_1(C_19,B_18))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2079,plain,(
    ! [A_231,C_232,B_233,D_234] :
      ( r2_hidden(A_231,k10_relat_1(C_232,B_233))
      | ~ r2_hidden(D_234,B_233)
      | ~ r2_hidden(k4_tarski(A_231,D_234),C_232)
      | ~ r2_hidden(D_234,k2_relat_1(C_232))
      | ~ v1_relat_1(C_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3355,plain,(
    ! [A_310,C_311,B_312,A_313] :
      ( r2_hidden(A_310,k10_relat_1(C_311,B_312))
      | ~ r2_hidden(k4_tarski(A_310,'#skF_1'(A_313,B_312)),C_311)
      | ~ r2_hidden('#skF_1'(A_313,B_312),k2_relat_1(C_311))
      | ~ v1_relat_1(C_311)
      | r1_xboole_0(A_313,B_312) ) ),
    inference(resolution,[status(thm)],[c_6,c_2079])).

tff(c_43493,plain,(
    ! [A_1023,B_1024,B_1025,C_1026] :
      ( r2_hidden('#skF_2'('#skF_1'(A_1023,B_1024),B_1025,C_1026),k10_relat_1(C_1026,B_1024))
      | ~ r2_hidden('#skF_1'(A_1023,B_1024),k2_relat_1(C_1026))
      | r1_xboole_0(A_1023,B_1024)
      | ~ r2_hidden('#skF_1'(A_1023,B_1024),k9_relat_1(C_1026,B_1025))
      | ~ v1_relat_1(C_1026) ) ),
    inference(resolution,[status(thm)],[c_28,c_3355])).

tff(c_43645,plain,(
    ! [A_1023,B_1025] :
      ( r2_hidden('#skF_2'('#skF_1'(A_1023,'#skF_4'),B_1025,'#skF_5'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_1023,'#skF_4'),k2_relat_1('#skF_5'))
      | r1_xboole_0(A_1023,'#skF_4')
      | ~ r2_hidden('#skF_1'(A_1023,'#skF_4'),k9_relat_1('#skF_5',B_1025))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1055,c_43493])).

tff(c_43735,plain,(
    ! [A_1023,B_1025] :
      ( r2_hidden('#skF_2'('#skF_1'(A_1023,'#skF_4'),B_1025,'#skF_5'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_1023,'#skF_4'),k2_relat_1('#skF_5'))
      | r1_xboole_0(A_1023,'#skF_4')
      | ~ r2_hidden('#skF_1'(A_1023,'#skF_4'),k9_relat_1('#skF_5',B_1025)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_43645])).

tff(c_44925,plain,(
    ! [A_1035,B_1036] :
      ( ~ r2_hidden('#skF_1'(A_1035,'#skF_4'),k2_relat_1('#skF_5'))
      | r1_xboole_0(A_1035,'#skF_4')
      | ~ r2_hidden('#skF_1'(A_1035,'#skF_4'),k9_relat_1('#skF_5',B_1036)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_43735])).

tff(c_44943,plain,(
    ! [A_1035] :
      ( ~ r2_hidden('#skF_1'(A_1035,'#skF_4'),k2_relat_1('#skF_5'))
      | r1_xboole_0(A_1035,'#skF_4')
      | ~ r2_hidden('#skF_1'(A_1035,'#skF_4'),k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_44925])).

tff(c_44951,plain,(
    ! [A_1037] :
      ( r1_xboole_0(A_1037,'#skF_4')
      | ~ r2_hidden('#skF_1'(A_1037,'#skF_4'),k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44943])).

tff(c_44971,plain,(
    r1_xboole_0(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_44951])).

tff(c_44984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1054,c_1054,c_44971])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.60/5.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.60/5.02  
% 11.60/5.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.60/5.02  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 11.60/5.02  
% 11.60/5.02  %Foreground sorts:
% 11.60/5.02  
% 11.60/5.02  
% 11.60/5.02  %Background operators:
% 11.60/5.02  
% 11.60/5.02  
% 11.60/5.02  %Foreground operators:
% 11.60/5.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.60/5.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.60/5.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.60/5.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.60/5.02  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.60/5.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.60/5.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.60/5.02  tff('#skF_5', type, '#skF_5': $i).
% 11.60/5.02  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.60/5.02  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.60/5.02  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.60/5.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.60/5.02  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 11.60/5.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.60/5.02  tff('#skF_4', type, '#skF_4': $i).
% 11.60/5.02  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.60/5.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.60/5.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.60/5.02  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.60/5.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.60/5.02  
% 11.75/5.03  tff(f_109, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 11.75/5.03  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 11.75/5.03  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 11.75/5.03  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 11.75/5.03  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.75/5.03  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 11.75/5.03  tff(f_94, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 11.75/5.03  tff(f_90, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 11.75/5.03  tff(f_55, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 11.75/5.03  tff(f_64, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 11.75/5.03  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 11.75/5.03  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 11.75/5.03  tff(c_50, plain, (~r1_xboole_0(k2_relat_1('#skF_5'), '#skF_4') | k10_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.75/5.03  tff(c_99, plain, (k10_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 11.75/5.03  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.75/5.03  tff(c_48, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.75/5.03  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.75/5.03  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.75/5.03  tff(c_144, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.75/5.03  tff(c_170, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_144])).
% 11.75/5.03  tff(c_174, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_170])).
% 11.75/5.03  tff(c_56, plain, (k10_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.75/5.03  tff(c_255, plain, (r1_xboole_0(k2_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_99, c_56])).
% 11.75/5.03  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.75/5.03  tff(c_261, plain, (k4_xboole_0(k2_relat_1('#skF_5'), '#skF_4')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_255, c_18])).
% 11.75/5.03  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.75/5.03  tff(c_297, plain, (k4_xboole_0(k2_relat_1('#skF_5'), k2_relat_1('#skF_5'))=k3_xboole_0(k2_relat_1('#skF_5'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_261, c_14])).
% 11.75/5.03  tff(c_300, plain, (k3_xboole_0(k2_relat_1('#skF_5'), '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_174, c_297])).
% 11.75/5.03  tff(c_376, plain, (![B_70, A_71]: (k10_relat_1(B_70, k3_xboole_0(k2_relat_1(B_70), A_71))=k10_relat_1(B_70, A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.75/5.03  tff(c_385, plain, (k10_relat_1('#skF_5', k1_xboole_0)=k10_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_300, c_376])).
% 11.75/5.03  tff(c_397, plain, (k10_relat_1('#skF_5', k1_xboole_0)=k10_relat_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_385])).
% 11.75/5.03  tff(c_535, plain, (![A_97, B_98, C_99]: (r2_hidden('#skF_3'(A_97, B_98, C_99), B_98) | ~r2_hidden(A_97, k10_relat_1(C_99, B_98)) | ~v1_relat_1(C_99))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.75/5.03  tff(c_16, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.75/5.03  tff(c_78, plain, (![A_40, B_41]: (~r2_hidden(A_40, B_41) | ~r1_xboole_0(k1_tarski(A_40), B_41))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.75/5.03  tff(c_83, plain, (![A_40]: (~r2_hidden(A_40, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_78])).
% 11.75/5.03  tff(c_911, plain, (![A_119, C_120]: (~r2_hidden(A_119, k10_relat_1(C_120, k1_xboole_0)) | ~v1_relat_1(C_120))), inference(resolution, [status(thm)], [c_535, c_83])).
% 11.75/5.03  tff(c_922, plain, (![A_119]: (~r2_hidden(A_119, k10_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_397, c_911])).
% 11.75/5.03  tff(c_959, plain, (![A_124]: (~r2_hidden(A_124, k10_relat_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_922])).
% 11.75/5.03  tff(c_980, plain, (![A_125]: (r1_xboole_0(A_125, k10_relat_1('#skF_5', '#skF_4')))), inference(resolution, [status(thm)], [c_6, c_959])).
% 11.75/5.03  tff(c_1010, plain, (![A_129]: (k4_xboole_0(A_129, k10_relat_1('#skF_5', '#skF_4'))=A_129)), inference(resolution, [status(thm)], [c_980, c_18])).
% 11.75/5.03  tff(c_1029, plain, (k10_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1010, c_174])).
% 11.75/5.03  tff(c_1053, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_1029])).
% 11.75/5.03  tff(c_1054, plain, (~r1_xboole_0(k2_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 11.75/5.03  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.75/5.03  tff(c_32, plain, (![A_23]: (k9_relat_1(A_23, k1_relat_1(A_23))=k2_relat_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.75/5.03  tff(c_1055, plain, (k10_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 11.75/5.03  tff(c_28, plain, (![A_17, B_18, C_19]: (r2_hidden(k4_tarski('#skF_2'(A_17, B_18, C_19), A_17), C_19) | ~r2_hidden(A_17, k9_relat_1(C_19, B_18)) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.75/5.03  tff(c_2079, plain, (![A_231, C_232, B_233, D_234]: (r2_hidden(A_231, k10_relat_1(C_232, B_233)) | ~r2_hidden(D_234, B_233) | ~r2_hidden(k4_tarski(A_231, D_234), C_232) | ~r2_hidden(D_234, k2_relat_1(C_232)) | ~v1_relat_1(C_232))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.75/5.03  tff(c_3355, plain, (![A_310, C_311, B_312, A_313]: (r2_hidden(A_310, k10_relat_1(C_311, B_312)) | ~r2_hidden(k4_tarski(A_310, '#skF_1'(A_313, B_312)), C_311) | ~r2_hidden('#skF_1'(A_313, B_312), k2_relat_1(C_311)) | ~v1_relat_1(C_311) | r1_xboole_0(A_313, B_312))), inference(resolution, [status(thm)], [c_6, c_2079])).
% 11.75/5.03  tff(c_43493, plain, (![A_1023, B_1024, B_1025, C_1026]: (r2_hidden('#skF_2'('#skF_1'(A_1023, B_1024), B_1025, C_1026), k10_relat_1(C_1026, B_1024)) | ~r2_hidden('#skF_1'(A_1023, B_1024), k2_relat_1(C_1026)) | r1_xboole_0(A_1023, B_1024) | ~r2_hidden('#skF_1'(A_1023, B_1024), k9_relat_1(C_1026, B_1025)) | ~v1_relat_1(C_1026))), inference(resolution, [status(thm)], [c_28, c_3355])).
% 11.75/5.03  tff(c_43645, plain, (![A_1023, B_1025]: (r2_hidden('#skF_2'('#skF_1'(A_1023, '#skF_4'), B_1025, '#skF_5'), k1_xboole_0) | ~r2_hidden('#skF_1'(A_1023, '#skF_4'), k2_relat_1('#skF_5')) | r1_xboole_0(A_1023, '#skF_4') | ~r2_hidden('#skF_1'(A_1023, '#skF_4'), k9_relat_1('#skF_5', B_1025)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1055, c_43493])).
% 11.75/5.03  tff(c_43735, plain, (![A_1023, B_1025]: (r2_hidden('#skF_2'('#skF_1'(A_1023, '#skF_4'), B_1025, '#skF_5'), k1_xboole_0) | ~r2_hidden('#skF_1'(A_1023, '#skF_4'), k2_relat_1('#skF_5')) | r1_xboole_0(A_1023, '#skF_4') | ~r2_hidden('#skF_1'(A_1023, '#skF_4'), k9_relat_1('#skF_5', B_1025)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_43645])).
% 11.75/5.03  tff(c_44925, plain, (![A_1035, B_1036]: (~r2_hidden('#skF_1'(A_1035, '#skF_4'), k2_relat_1('#skF_5')) | r1_xboole_0(A_1035, '#skF_4') | ~r2_hidden('#skF_1'(A_1035, '#skF_4'), k9_relat_1('#skF_5', B_1036)))), inference(negUnitSimplification, [status(thm)], [c_83, c_43735])).
% 11.75/5.03  tff(c_44943, plain, (![A_1035]: (~r2_hidden('#skF_1'(A_1035, '#skF_4'), k2_relat_1('#skF_5')) | r1_xboole_0(A_1035, '#skF_4') | ~r2_hidden('#skF_1'(A_1035, '#skF_4'), k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_44925])).
% 11.75/5.03  tff(c_44951, plain, (![A_1037]: (r1_xboole_0(A_1037, '#skF_4') | ~r2_hidden('#skF_1'(A_1037, '#skF_4'), k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44943])).
% 11.75/5.03  tff(c_44971, plain, (r1_xboole_0(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_8, c_44951])).
% 11.75/5.03  tff(c_44984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1054, c_1054, c_44971])).
% 11.75/5.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.75/5.03  
% 11.75/5.03  Inference rules
% 11.75/5.03  ----------------------
% 11.75/5.03  #Ref     : 0
% 11.75/5.03  #Sup     : 10335
% 11.75/5.03  #Fact    : 0
% 11.75/5.03  #Define  : 0
% 11.75/5.03  #Split   : 7
% 11.75/5.03  #Chain   : 0
% 11.75/5.03  #Close   : 0
% 11.75/5.03  
% 11.75/5.03  Ordering : KBO
% 11.75/5.03  
% 11.75/5.03  Simplification rules
% 11.75/5.03  ----------------------
% 11.75/5.03  #Subsume      : 4194
% 11.75/5.03  #Demod        : 5838
% 11.75/5.03  #Tautology    : 4642
% 11.75/5.03  #SimpNegUnit  : 32
% 11.75/5.03  #BackRed      : 0
% 11.75/5.03  
% 11.75/5.03  #Partial instantiations: 0
% 11.75/5.03  #Strategies tried      : 1
% 11.75/5.03  
% 11.75/5.03  Timing (in seconds)
% 11.75/5.03  ----------------------
% 11.75/5.03  Preprocessing        : 0.29
% 11.75/5.03  Parsing              : 0.16
% 11.75/5.03  CNF conversion       : 0.02
% 11.75/5.04  Main loop            : 3.97
% 11.75/5.04  Inferencing          : 1.12
% 11.75/5.04  Reduction            : 1.17
% 11.75/5.04  Demodulation         : 0.78
% 11.75/5.04  BG Simplification    : 0.09
% 11.75/5.04  Subsumption          : 1.39
% 11.75/5.04  Abstraction          : 0.17
% 11.75/5.04  MUC search           : 0.00
% 11.75/5.04  Cooper               : 0.00
% 11.75/5.04  Total                : 4.29
% 11.75/5.04  Index Insertion      : 0.00
% 11.75/5.04  Index Deletion       : 0.00
% 11.75/5.04  Index Matching       : 0.00
% 11.75/5.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
