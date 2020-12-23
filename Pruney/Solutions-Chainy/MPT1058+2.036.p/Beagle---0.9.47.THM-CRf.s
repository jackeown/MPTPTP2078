%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:26 EST 2020

% Result     : Theorem 8.99s
% Output     : CNFRefutation 8.99s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 158 expanded)
%              Number of leaves         :   41 (  77 expanded)
%              Depth                    :   14
%              Number of atoms          :  118 ( 265 expanded)
%              Number of equality atoms :   32 (  90 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_70,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') != k10_relat_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_76,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_72,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_56,plain,(
    ! [A_56] : v1_relat_1(k6_relat_1(A_56)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    ! [A_43] : k1_relat_1(k6_relat_1(A_43)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    ! [A_43] : k2_relat_1(k6_relat_1(A_43)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_139,plain,(
    ! [A_83] :
      ( k10_relat_1(A_83,k2_relat_1(A_83)) = k1_relat_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_148,plain,(
    ! [A_43] :
      ( k10_relat_1(k6_relat_1(A_43),A_43) = k1_relat_1(k6_relat_1(A_43))
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_139])).

tff(c_152,plain,(
    ! [A_43] : k10_relat_1(k6_relat_1(A_43),A_43) = A_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_34,c_148])).

tff(c_58,plain,(
    ! [A_56] : v1_funct_1(k6_relat_1(A_56)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2104,plain,(
    ! [B_213,A_214] :
      ( k9_relat_1(B_213,k10_relat_1(B_213,A_214)) = A_214
      | ~ r1_tarski(A_214,k2_relat_1(B_213))
      | ~ v1_funct_1(B_213)
      | ~ v1_relat_1(B_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2124,plain,(
    ! [A_43,A_214] :
      ( k9_relat_1(k6_relat_1(A_43),k10_relat_1(k6_relat_1(A_43),A_214)) = A_214
      | ~ r1_tarski(A_214,A_43)
      | ~ v1_funct_1(k6_relat_1(A_43))
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2104])).

tff(c_2137,plain,(
    ! [A_215,A_216] :
      ( k9_relat_1(k6_relat_1(A_215),k10_relat_1(k6_relat_1(A_215),A_216)) = A_216
      | ~ r1_tarski(A_216,A_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_2124])).

tff(c_2152,plain,(
    ! [A_43] :
      ( k9_relat_1(k6_relat_1(A_43),A_43) = A_43
      | ~ r1_tarski(A_43,A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_2137])).

tff(c_2164,plain,(
    ! [A_43] : k9_relat_1(k6_relat_1(A_43),A_43) = A_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2152])).

tff(c_3752,plain,(
    ! [A_293,C_294,B_295] :
      ( r1_tarski(A_293,k10_relat_1(C_294,B_295))
      | ~ r1_tarski(k9_relat_1(C_294,A_293),B_295)
      | ~ r1_tarski(A_293,k1_relat_1(C_294))
      | ~ v1_funct_1(C_294)
      | ~ v1_relat_1(C_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3774,plain,(
    ! [A_43,B_295] :
      ( r1_tarski(A_43,k10_relat_1(k6_relat_1(A_43),B_295))
      | ~ r1_tarski(A_43,B_295)
      | ~ r1_tarski(A_43,k1_relat_1(k6_relat_1(A_43)))
      | ~ v1_funct_1(k6_relat_1(A_43))
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2164,c_3752])).

tff(c_3805,plain,(
    ! [A_43,B_295] :
      ( r1_tarski(A_43,k10_relat_1(k6_relat_1(A_43),B_295))
      | ~ r1_tarski(A_43,B_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_12,c_34,c_3774])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1292,plain,(
    ! [D_175,A_176,B_177] :
      ( r2_hidden(D_175,k1_relat_1(A_176))
      | ~ r2_hidden(D_175,k10_relat_1(A_176,B_177))
      | ~ v1_funct_1(A_176)
      | ~ v1_relat_1(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10687,plain,(
    ! [A_474,B_475,B_476] :
      ( r2_hidden('#skF_1'(k10_relat_1(A_474,B_475),B_476),k1_relat_1(A_474))
      | ~ v1_funct_1(A_474)
      | ~ v1_relat_1(A_474)
      | r1_tarski(k10_relat_1(A_474,B_475),B_476) ) ),
    inference(resolution,[status(thm)],[c_6,c_1292])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10719,plain,(
    ! [A_477,B_478] :
      ( ~ v1_funct_1(A_477)
      | ~ v1_relat_1(A_477)
      | r1_tarski(k10_relat_1(A_477,B_478),k1_relat_1(A_477)) ) ),
    inference(resolution,[status(thm)],[c_10687,c_4])).

tff(c_10753,plain,(
    ! [A_43,B_478] :
      ( ~ v1_funct_1(k6_relat_1(A_43))
      | ~ v1_relat_1(k6_relat_1(A_43))
      | r1_tarski(k10_relat_1(k6_relat_1(A_43),B_478),A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_10719])).

tff(c_10766,plain,(
    ! [A_479,B_480] : r1_tarski(k10_relat_1(k6_relat_1(A_479),B_480),A_479) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_10753])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14968,plain,(
    ! [A_584,B_585] :
      ( k10_relat_1(k6_relat_1(A_584),B_585) = A_584
      | ~ r1_tarski(A_584,k10_relat_1(k6_relat_1(A_584),B_585)) ) ),
    inference(resolution,[status(thm)],[c_10766,c_8])).

tff(c_15016,plain,(
    ! [A_586,B_587] :
      ( k10_relat_1(k6_relat_1(A_586),B_587) = A_586
      | ~ r1_tarski(A_586,B_587) ) ),
    inference(resolution,[status(thm)],[c_3805,c_14968])).

tff(c_2902,plain,(
    ! [A_255,B_256] :
      ( k3_xboole_0(A_255,k9_relat_1(B_256,k1_relat_1(B_256))) = k9_relat_1(B_256,k10_relat_1(B_256,A_255))
      | ~ v1_funct_1(B_256)
      | ~ v1_relat_1(B_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2911,plain,(
    ! [A_43,A_255] :
      ( k9_relat_1(k6_relat_1(A_43),k10_relat_1(k6_relat_1(A_43),A_255)) = k3_xboole_0(A_255,k9_relat_1(k6_relat_1(A_43),A_43))
      | ~ v1_funct_1(k6_relat_1(A_43))
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2902])).

tff(c_2915,plain,(
    ! [A_43,A_255] : k9_relat_1(k6_relat_1(A_43),k10_relat_1(k6_relat_1(A_43),A_255)) = k3_xboole_0(A_255,A_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_2164,c_2911])).

tff(c_15169,plain,(
    ! [A_586,B_587] :
      ( k9_relat_1(k6_relat_1(A_586),A_586) = k3_xboole_0(B_587,A_586)
      | ~ r1_tarski(A_586,B_587) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15016,c_2915])).

tff(c_15272,plain,(
    ! [B_588,A_589] :
      ( k3_xboole_0(B_588,A_589) = A_589
      | ~ r1_tarski(A_589,B_588) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2164,c_15169])).

tff(c_15524,plain,(
    k3_xboole_0('#skF_5',k10_relat_1('#skF_4','#skF_6')) = k10_relat_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_15272])).

tff(c_60,plain,(
    ! [A_57,C_59,B_58] :
      ( k3_xboole_0(A_57,k10_relat_1(C_59,B_58)) = k10_relat_1(k7_relat_1(C_59,A_57),B_58)
      | ~ v1_relat_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_16317,plain,
    ( k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_15524,c_60])).

tff(c_16349,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_16317])).

tff(c_16351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_16349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:08:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.99/3.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.99/3.44  
% 8.99/3.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.99/3.44  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 8.99/3.44  
% 8.99/3.44  %Foreground sorts:
% 8.99/3.44  
% 8.99/3.44  
% 8.99/3.44  %Background operators:
% 8.99/3.44  
% 8.99/3.44  
% 8.99/3.44  %Foreground operators:
% 8.99/3.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.99/3.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.99/3.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.99/3.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.99/3.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.99/3.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.99/3.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.99/3.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.99/3.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.99/3.44  tff('#skF_5', type, '#skF_5': $i).
% 8.99/3.44  tff('#skF_6', type, '#skF_6': $i).
% 8.99/3.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.99/3.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.99/3.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.99/3.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.99/3.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.99/3.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.99/3.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.99/3.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.99/3.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.99/3.44  tff('#skF_4', type, '#skF_4': $i).
% 8.99/3.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.99/3.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.99/3.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.99/3.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.99/3.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.99/3.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.99/3.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.99/3.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.99/3.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.99/3.44  
% 8.99/3.45  tff(f_130, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 8.99/3.45  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.99/3.45  tff(f_86, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 8.99/3.45  tff(f_68, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.99/3.45  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 8.99/3.45  tff(f_104, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 8.99/3.45  tff(f_120, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 8.99/3.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.99/3.45  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 8.99/3.45  tff(f_110, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 8.99/3.45  tff(f_90, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 8.99/3.45  tff(c_70, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.99/3.45  tff(c_76, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.99/3.45  tff(c_72, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.99/3.45  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.99/3.45  tff(c_56, plain, (![A_56]: (v1_relat_1(k6_relat_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.99/3.45  tff(c_34, plain, (![A_43]: (k1_relat_1(k6_relat_1(A_43))=A_43)), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.99/3.45  tff(c_36, plain, (![A_43]: (k2_relat_1(k6_relat_1(A_43))=A_43)), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.99/3.45  tff(c_139, plain, (![A_83]: (k10_relat_1(A_83, k2_relat_1(A_83))=k1_relat_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.99/3.45  tff(c_148, plain, (![A_43]: (k10_relat_1(k6_relat_1(A_43), A_43)=k1_relat_1(k6_relat_1(A_43)) | ~v1_relat_1(k6_relat_1(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_139])).
% 8.99/3.45  tff(c_152, plain, (![A_43]: (k10_relat_1(k6_relat_1(A_43), A_43)=A_43)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_34, c_148])).
% 8.99/3.45  tff(c_58, plain, (![A_56]: (v1_funct_1(k6_relat_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.99/3.45  tff(c_2104, plain, (![B_213, A_214]: (k9_relat_1(B_213, k10_relat_1(B_213, A_214))=A_214 | ~r1_tarski(A_214, k2_relat_1(B_213)) | ~v1_funct_1(B_213) | ~v1_relat_1(B_213))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.99/3.45  tff(c_2124, plain, (![A_43, A_214]: (k9_relat_1(k6_relat_1(A_43), k10_relat_1(k6_relat_1(A_43), A_214))=A_214 | ~r1_tarski(A_214, A_43) | ~v1_funct_1(k6_relat_1(A_43)) | ~v1_relat_1(k6_relat_1(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2104])).
% 8.99/3.45  tff(c_2137, plain, (![A_215, A_216]: (k9_relat_1(k6_relat_1(A_215), k10_relat_1(k6_relat_1(A_215), A_216))=A_216 | ~r1_tarski(A_216, A_215))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_2124])).
% 8.99/3.45  tff(c_2152, plain, (![A_43]: (k9_relat_1(k6_relat_1(A_43), A_43)=A_43 | ~r1_tarski(A_43, A_43))), inference(superposition, [status(thm), theory('equality')], [c_152, c_2137])).
% 8.99/3.45  tff(c_2164, plain, (![A_43]: (k9_relat_1(k6_relat_1(A_43), A_43)=A_43)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2152])).
% 8.99/3.45  tff(c_3752, plain, (![A_293, C_294, B_295]: (r1_tarski(A_293, k10_relat_1(C_294, B_295)) | ~r1_tarski(k9_relat_1(C_294, A_293), B_295) | ~r1_tarski(A_293, k1_relat_1(C_294)) | ~v1_funct_1(C_294) | ~v1_relat_1(C_294))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.99/3.45  tff(c_3774, plain, (![A_43, B_295]: (r1_tarski(A_43, k10_relat_1(k6_relat_1(A_43), B_295)) | ~r1_tarski(A_43, B_295) | ~r1_tarski(A_43, k1_relat_1(k6_relat_1(A_43))) | ~v1_funct_1(k6_relat_1(A_43)) | ~v1_relat_1(k6_relat_1(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_2164, c_3752])).
% 8.99/3.45  tff(c_3805, plain, (![A_43, B_295]: (r1_tarski(A_43, k10_relat_1(k6_relat_1(A_43), B_295)) | ~r1_tarski(A_43, B_295))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_12, c_34, c_3774])).
% 8.99/3.45  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.99/3.45  tff(c_1292, plain, (![D_175, A_176, B_177]: (r2_hidden(D_175, k1_relat_1(A_176)) | ~r2_hidden(D_175, k10_relat_1(A_176, B_177)) | ~v1_funct_1(A_176) | ~v1_relat_1(A_176))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.99/3.45  tff(c_10687, plain, (![A_474, B_475, B_476]: (r2_hidden('#skF_1'(k10_relat_1(A_474, B_475), B_476), k1_relat_1(A_474)) | ~v1_funct_1(A_474) | ~v1_relat_1(A_474) | r1_tarski(k10_relat_1(A_474, B_475), B_476))), inference(resolution, [status(thm)], [c_6, c_1292])).
% 8.99/3.45  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.99/3.45  tff(c_10719, plain, (![A_477, B_478]: (~v1_funct_1(A_477) | ~v1_relat_1(A_477) | r1_tarski(k10_relat_1(A_477, B_478), k1_relat_1(A_477)))), inference(resolution, [status(thm)], [c_10687, c_4])).
% 8.99/3.45  tff(c_10753, plain, (![A_43, B_478]: (~v1_funct_1(k6_relat_1(A_43)) | ~v1_relat_1(k6_relat_1(A_43)) | r1_tarski(k10_relat_1(k6_relat_1(A_43), B_478), A_43))), inference(superposition, [status(thm), theory('equality')], [c_34, c_10719])).
% 8.99/3.45  tff(c_10766, plain, (![A_479, B_480]: (r1_tarski(k10_relat_1(k6_relat_1(A_479), B_480), A_479))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_10753])).
% 8.99/3.45  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.99/3.45  tff(c_14968, plain, (![A_584, B_585]: (k10_relat_1(k6_relat_1(A_584), B_585)=A_584 | ~r1_tarski(A_584, k10_relat_1(k6_relat_1(A_584), B_585)))), inference(resolution, [status(thm)], [c_10766, c_8])).
% 8.99/3.45  tff(c_15016, plain, (![A_586, B_587]: (k10_relat_1(k6_relat_1(A_586), B_587)=A_586 | ~r1_tarski(A_586, B_587))), inference(resolution, [status(thm)], [c_3805, c_14968])).
% 8.99/3.45  tff(c_2902, plain, (![A_255, B_256]: (k3_xboole_0(A_255, k9_relat_1(B_256, k1_relat_1(B_256)))=k9_relat_1(B_256, k10_relat_1(B_256, A_255)) | ~v1_funct_1(B_256) | ~v1_relat_1(B_256))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.99/3.45  tff(c_2911, plain, (![A_43, A_255]: (k9_relat_1(k6_relat_1(A_43), k10_relat_1(k6_relat_1(A_43), A_255))=k3_xboole_0(A_255, k9_relat_1(k6_relat_1(A_43), A_43)) | ~v1_funct_1(k6_relat_1(A_43)) | ~v1_relat_1(k6_relat_1(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2902])).
% 8.99/3.45  tff(c_2915, plain, (![A_43, A_255]: (k9_relat_1(k6_relat_1(A_43), k10_relat_1(k6_relat_1(A_43), A_255))=k3_xboole_0(A_255, A_43))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_2164, c_2911])).
% 8.99/3.45  tff(c_15169, plain, (![A_586, B_587]: (k9_relat_1(k6_relat_1(A_586), A_586)=k3_xboole_0(B_587, A_586) | ~r1_tarski(A_586, B_587))), inference(superposition, [status(thm), theory('equality')], [c_15016, c_2915])).
% 8.99/3.45  tff(c_15272, plain, (![B_588, A_589]: (k3_xboole_0(B_588, A_589)=A_589 | ~r1_tarski(A_589, B_588))), inference(demodulation, [status(thm), theory('equality')], [c_2164, c_15169])).
% 8.99/3.45  tff(c_15524, plain, (k3_xboole_0('#skF_5', k10_relat_1('#skF_4', '#skF_6'))=k10_relat_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_72, c_15272])).
% 8.99/3.45  tff(c_60, plain, (![A_57, C_59, B_58]: (k3_xboole_0(A_57, k10_relat_1(C_59, B_58))=k10_relat_1(k7_relat_1(C_59, A_57), B_58) | ~v1_relat_1(C_59))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.99/3.45  tff(c_16317, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_15524, c_60])).
% 8.99/3.45  tff(c_16349, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_16317])).
% 8.99/3.45  tff(c_16351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_16349])).
% 8.99/3.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.99/3.45  
% 8.99/3.45  Inference rules
% 8.99/3.45  ----------------------
% 8.99/3.45  #Ref     : 0
% 8.99/3.45  #Sup     : 4121
% 8.99/3.45  #Fact    : 0
% 8.99/3.45  #Define  : 0
% 8.99/3.45  #Split   : 1
% 8.99/3.45  #Chain   : 0
% 8.99/3.45  #Close   : 0
% 8.99/3.45  
% 8.99/3.45  Ordering : KBO
% 8.99/3.45  
% 8.99/3.46  Simplification rules
% 8.99/3.46  ----------------------
% 8.99/3.46  #Subsume      : 493
% 8.99/3.46  #Demod        : 1829
% 8.99/3.46  #Tautology    : 1531
% 8.99/3.46  #SimpNegUnit  : 1
% 8.99/3.46  #BackRed      : 19
% 8.99/3.46  
% 8.99/3.46  #Partial instantiations: 0
% 8.99/3.46  #Strategies tried      : 1
% 8.99/3.46  
% 8.99/3.46  Timing (in seconds)
% 8.99/3.46  ----------------------
% 8.99/3.46  Preprocessing        : 0.35
% 8.99/3.46  Parsing              : 0.18
% 8.99/3.46  CNF conversion       : 0.03
% 8.99/3.46  Main loop            : 2.33
% 8.99/3.46  Inferencing          : 0.59
% 8.99/3.46  Reduction            : 0.93
% 8.99/3.46  Demodulation         : 0.75
% 8.99/3.46  BG Simplification    : 0.09
% 8.99/3.46  Subsumption          : 0.56
% 8.99/3.46  Abstraction          : 0.10
% 8.99/3.46  MUC search           : 0.00
% 8.99/3.46  Cooper               : 0.00
% 8.99/3.46  Total                : 2.71
% 8.99/3.46  Index Insertion      : 0.00
% 8.99/3.46  Index Deletion       : 0.00
% 8.99/3.46  Index Matching       : 0.00
% 8.99/3.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
