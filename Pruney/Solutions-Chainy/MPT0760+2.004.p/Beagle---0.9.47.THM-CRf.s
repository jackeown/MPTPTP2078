%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:34 EST 2020

% Result     : Theorem 6.38s
% Output     : CNFRefutation 6.38s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 215 expanded)
%              Number of leaves         :   29 (  82 expanded)
%              Depth                    :   22
%              Number of atoms          :  120 ( 474 expanded)
%              Number of equality atoms :   38 ( 175 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k3_xboole_0 > k1_wellord1 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

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

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k3_relat_1(B))
          | k1_wellord1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord1)).

tff(f_60,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( ~ ( A = k1_xboole_0
            & B != k1_xboole_0 )
        & ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ~ ( B = k1_relat_1(C)
                & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_34,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( ( k1_relat_1(A) = k1_xboole_0
              & k1_relat_1(B) = k1_xboole_0 )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t196_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_56,plain,(
    k1_wellord1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_60,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26,plain,(
    ! [A_15] : k1_relat_1('#skF_2'(A_15,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    ! [A_15] : v1_relat_1('#skF_2'(A_15,k1_xboole_0)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_87,plain,(
    ! [A_37,B_38] :
      ( v1_relat_1(k3_xboole_0(A_37,B_38))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_90,plain,(
    ! [A_6] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_87])).

tff(c_91,plain,(
    ! [A_6] : ~ v1_relat_1(A_6) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_96,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_34])).

tff(c_97,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_135,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | k1_relat_1(B_61) != k1_xboole_0
      | k1_relat_1(A_62) != k1_xboole_0
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_137,plain,(
    ! [A_62] :
      ( k1_xboole_0 = A_62
      | k1_relat_1(k1_xboole_0) != k1_xboole_0
      | k1_relat_1(A_62) != k1_xboole_0
      | ~ v1_relat_1(A_62) ) ),
    inference(resolution,[status(thm)],[c_97,c_135])).

tff(c_155,plain,(
    ! [A_63] :
      ( k1_xboole_0 = A_63
      | k1_relat_1(A_63) != k1_xboole_0
      | ~ v1_relat_1(A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_137])).

tff(c_167,plain,(
    ! [A_15] :
      ( '#skF_2'(A_15,k1_xboole_0) = k1_xboole_0
      | k1_relat_1('#skF_2'(A_15,k1_xboole_0)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_155])).

tff(c_179,plain,(
    ! [A_15] : '#skF_2'(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_167])).

tff(c_22,plain,(
    ! [A_15] : r1_tarski(k2_relat_1('#skF_2'(A_15,k1_xboole_0)),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_181,plain,(
    ! [A_15] : r1_tarski(k2_relat_1(k1_xboole_0),A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_22])).

tff(c_185,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_181])).

tff(c_516,plain,(
    ! [A_111,B_112,C_113] :
      ( r2_hidden(k4_tarski('#skF_3'(A_111,B_112,C_113),B_112),A_111)
      | r2_hidden('#skF_4'(A_111,B_112,C_113),C_113)
      | k1_wellord1(A_111,B_112) = C_113
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_14,plain,(
    ! [B_13,C_14,A_12] :
      ( r2_hidden(B_13,k3_relat_1(C_14))
      | ~ r2_hidden(k4_tarski(A_12,B_13),C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1132,plain,(
    ! [B_184,A_185,C_186] :
      ( r2_hidden(B_184,k3_relat_1(A_185))
      | r2_hidden('#skF_4'(A_185,B_184,C_186),C_186)
      | k1_wellord1(A_185,B_184) = C_186
      | ~ v1_relat_1(A_185) ) ),
    inference(resolution,[status(thm)],[c_516,c_14])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5661,plain,(
    ! [A_4795,B_4796,C_4797,B_4798] :
      ( r2_hidden('#skF_4'(A_4795,B_4796,C_4797),B_4798)
      | ~ r1_tarski(C_4797,B_4798)
      | r2_hidden(B_4796,k3_relat_1(A_4795))
      | k1_wellord1(A_4795,B_4796) = C_4797
      | ~ v1_relat_1(A_4795) ) ),
    inference(resolution,[status(thm)],[c_1132,c_2])).

tff(c_215,plain,(
    ! [D_66,B_67,A_68] :
      ( r2_hidden(k4_tarski(D_66,B_67),A_68)
      | ~ r2_hidden(D_66,k1_wellord1(A_68,B_67))
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_736,plain,(
    ! [D_139,B_140,B_141,A_142] :
      ( r2_hidden(k4_tarski(D_139,B_140),B_141)
      | ~ r1_tarski(A_142,B_141)
      | ~ r2_hidden(D_139,k1_wellord1(A_142,B_140))
      | ~ v1_relat_1(A_142) ) ),
    inference(resolution,[status(thm)],[c_215,c_2])).

tff(c_746,plain,(
    ! [D_139,B_140,A_15] :
      ( r2_hidden(k4_tarski(D_139,B_140),A_15)
      | ~ r2_hidden(D_139,k1_wellord1(k1_xboole_0,B_140))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_185,c_736])).

tff(c_760,plain,(
    ! [D_143,B_144,A_145] :
      ( r2_hidden(k4_tarski(D_143,B_144),A_145)
      | ~ r2_hidden(D_143,k1_wellord1(k1_xboole_0,B_144)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_746])).

tff(c_42,plain,(
    ! [D_29,A_18] :
      ( ~ r2_hidden(D_29,k1_wellord1(A_18,D_29))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_792,plain,(
    ! [A_18,D_143,B_144] :
      ( ~ v1_relat_1(A_18)
      | ~ r2_hidden(D_143,k1_wellord1(k1_xboole_0,B_144)) ) ),
    inference(resolution,[status(thm)],[c_760,c_42])).

tff(c_793,plain,(
    ! [D_143,B_144] : ~ r2_hidden(D_143,k1_wellord1(k1_xboole_0,B_144)) ),
    inference(splitLeft,[status(thm)],[c_792])).

tff(c_1159,plain,(
    ! [B_187,A_188,B_189] :
      ( r2_hidden(B_187,k3_relat_1(A_188))
      | k1_wellord1(k1_xboole_0,B_189) = k1_wellord1(A_188,B_187)
      | ~ v1_relat_1(A_188) ) ),
    inference(resolution,[status(thm)],[c_1132,c_793])).

tff(c_58,plain,(
    ~ r2_hidden('#skF_5',k3_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1191,plain,(
    ! [B_189] :
      ( k1_wellord1(k1_xboole_0,B_189) = k1_wellord1('#skF_6','#skF_5')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1159,c_58])).

tff(c_1343,plain,(
    ! [B_189] : k1_wellord1(k1_xboole_0,B_189) = k1_wellord1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1191])).

tff(c_1398,plain,(
    ! [D_143] : ~ r2_hidden(D_143,k1_wellord1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1343,c_793])).

tff(c_5703,plain,(
    ! [C_4799,B_4800,A_4801] :
      ( ~ r1_tarski(C_4799,k1_wellord1('#skF_6','#skF_5'))
      | r2_hidden(B_4800,k3_relat_1(A_4801))
      | k1_wellord1(A_4801,B_4800) = C_4799
      | ~ v1_relat_1(A_4801) ) ),
    inference(resolution,[status(thm)],[c_5661,c_1398])).

tff(c_5768,plain,(
    ! [B_4802,A_4803] :
      ( r2_hidden(B_4802,k3_relat_1(A_4803))
      | k1_wellord1(A_4803,B_4802) = k1_xboole_0
      | ~ v1_relat_1(A_4803) ) ),
    inference(resolution,[status(thm)],[c_185,c_5703])).

tff(c_5803,plain,
    ( k1_wellord1('#skF_6','#skF_5') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_5768,c_58])).

tff(c_5815,plain,(
    k1_wellord1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5803])).

tff(c_5817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_5815])).

tff(c_5818,plain,(
    ! [A_18] : ~ v1_relat_1(A_18) ),
    inference(splitRight,[status(thm)],[c_792])).

tff(c_5823,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5818,c_97])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:54:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.38/2.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.38/2.41  
% 6.38/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.38/2.42  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k3_xboole_0 > k1_wellord1 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 6.38/2.42  
% 6.38/2.42  %Foreground sorts:
% 6.38/2.42  
% 6.38/2.42  
% 6.38/2.42  %Background operators:
% 6.38/2.42  
% 6.38/2.42  
% 6.38/2.42  %Foreground operators:
% 6.38/2.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.38/2.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.38/2.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.38/2.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.38/2.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.38/2.42  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 6.38/2.42  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.38/2.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.38/2.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.38/2.42  tff('#skF_5', type, '#skF_5': $i).
% 6.38/2.42  tff('#skF_6', type, '#skF_6': $i).
% 6.38/2.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.38/2.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.38/2.42  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 6.38/2.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.38/2.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.38/2.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.38/2.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.38/2.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.38/2.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.38/2.42  
% 6.38/2.43  tff(f_97, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k3_relat_1(B)) | (k1_wellord1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_wellord1)).
% 6.38/2.43  tff(f_60, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 6.38/2.43  tff(f_77, axiom, (![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 6.38/2.43  tff(f_34, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.38/2.43  tff(f_38, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 6.38/2.43  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (((k1_relat_1(A) = k1_xboole_0) & (k1_relat_1(B) = k1_xboole_0)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t196_relat_1)).
% 6.38/2.43  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 6.38/2.43  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 6.38/2.43  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.38/2.43  tff(c_56, plain, (k1_wellord1('#skF_6', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.38/2.43  tff(c_60, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.38/2.43  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.38/2.43  tff(c_26, plain, (![A_15]: (k1_relat_1('#skF_2'(A_15, k1_xboole_0))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.38/2.43  tff(c_34, plain, (![A_15]: (v1_relat_1('#skF_2'(A_15, k1_xboole_0)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.38/2.43  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.38/2.43  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.38/2.43  tff(c_87, plain, (![A_37, B_38]: (v1_relat_1(k3_xboole_0(A_37, B_38)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.38/2.43  tff(c_90, plain, (![A_6]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_87])).
% 6.38/2.43  tff(c_91, plain, (![A_6]: (~v1_relat_1(A_6))), inference(splitLeft, [status(thm)], [c_90])).
% 6.38/2.43  tff(c_96, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_34])).
% 6.38/2.43  tff(c_97, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_90])).
% 6.38/2.43  tff(c_135, plain, (![B_61, A_62]: (B_61=A_62 | k1_relat_1(B_61)!=k1_xboole_0 | k1_relat_1(A_62)!=k1_xboole_0 | ~v1_relat_1(B_61) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.38/2.43  tff(c_137, plain, (![A_62]: (k1_xboole_0=A_62 | k1_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(A_62)!=k1_xboole_0 | ~v1_relat_1(A_62))), inference(resolution, [status(thm)], [c_97, c_135])).
% 6.38/2.43  tff(c_155, plain, (![A_63]: (k1_xboole_0=A_63 | k1_relat_1(A_63)!=k1_xboole_0 | ~v1_relat_1(A_63))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_137])).
% 6.38/2.43  tff(c_167, plain, (![A_15]: ('#skF_2'(A_15, k1_xboole_0)=k1_xboole_0 | k1_relat_1('#skF_2'(A_15, k1_xboole_0))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_155])).
% 6.38/2.43  tff(c_179, plain, (![A_15]: ('#skF_2'(A_15, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_167])).
% 6.38/2.43  tff(c_22, plain, (![A_15]: (r1_tarski(k2_relat_1('#skF_2'(A_15, k1_xboole_0)), A_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.38/2.43  tff(c_181, plain, (![A_15]: (r1_tarski(k2_relat_1(k1_xboole_0), A_15))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_22])).
% 6.38/2.43  tff(c_185, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_181])).
% 6.38/2.43  tff(c_516, plain, (![A_111, B_112, C_113]: (r2_hidden(k4_tarski('#skF_3'(A_111, B_112, C_113), B_112), A_111) | r2_hidden('#skF_4'(A_111, B_112, C_113), C_113) | k1_wellord1(A_111, B_112)=C_113 | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.38/2.43  tff(c_14, plain, (![B_13, C_14, A_12]: (r2_hidden(B_13, k3_relat_1(C_14)) | ~r2_hidden(k4_tarski(A_12, B_13), C_14) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.38/2.43  tff(c_1132, plain, (![B_184, A_185, C_186]: (r2_hidden(B_184, k3_relat_1(A_185)) | r2_hidden('#skF_4'(A_185, B_184, C_186), C_186) | k1_wellord1(A_185, B_184)=C_186 | ~v1_relat_1(A_185))), inference(resolution, [status(thm)], [c_516, c_14])).
% 6.38/2.43  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.38/2.43  tff(c_5661, plain, (![A_4795, B_4796, C_4797, B_4798]: (r2_hidden('#skF_4'(A_4795, B_4796, C_4797), B_4798) | ~r1_tarski(C_4797, B_4798) | r2_hidden(B_4796, k3_relat_1(A_4795)) | k1_wellord1(A_4795, B_4796)=C_4797 | ~v1_relat_1(A_4795))), inference(resolution, [status(thm)], [c_1132, c_2])).
% 6.38/2.43  tff(c_215, plain, (![D_66, B_67, A_68]: (r2_hidden(k4_tarski(D_66, B_67), A_68) | ~r2_hidden(D_66, k1_wellord1(A_68, B_67)) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.38/2.43  tff(c_736, plain, (![D_139, B_140, B_141, A_142]: (r2_hidden(k4_tarski(D_139, B_140), B_141) | ~r1_tarski(A_142, B_141) | ~r2_hidden(D_139, k1_wellord1(A_142, B_140)) | ~v1_relat_1(A_142))), inference(resolution, [status(thm)], [c_215, c_2])).
% 6.38/2.43  tff(c_746, plain, (![D_139, B_140, A_15]: (r2_hidden(k4_tarski(D_139, B_140), A_15) | ~r2_hidden(D_139, k1_wellord1(k1_xboole_0, B_140)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_185, c_736])).
% 6.38/2.43  tff(c_760, plain, (![D_143, B_144, A_145]: (r2_hidden(k4_tarski(D_143, B_144), A_145) | ~r2_hidden(D_143, k1_wellord1(k1_xboole_0, B_144)))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_746])).
% 6.38/2.43  tff(c_42, plain, (![D_29, A_18]: (~r2_hidden(D_29, k1_wellord1(A_18, D_29)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.38/2.43  tff(c_792, plain, (![A_18, D_143, B_144]: (~v1_relat_1(A_18) | ~r2_hidden(D_143, k1_wellord1(k1_xboole_0, B_144)))), inference(resolution, [status(thm)], [c_760, c_42])).
% 6.38/2.43  tff(c_793, plain, (![D_143, B_144]: (~r2_hidden(D_143, k1_wellord1(k1_xboole_0, B_144)))), inference(splitLeft, [status(thm)], [c_792])).
% 6.38/2.43  tff(c_1159, plain, (![B_187, A_188, B_189]: (r2_hidden(B_187, k3_relat_1(A_188)) | k1_wellord1(k1_xboole_0, B_189)=k1_wellord1(A_188, B_187) | ~v1_relat_1(A_188))), inference(resolution, [status(thm)], [c_1132, c_793])).
% 6.38/2.43  tff(c_58, plain, (~r2_hidden('#skF_5', k3_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.38/2.43  tff(c_1191, plain, (![B_189]: (k1_wellord1(k1_xboole_0, B_189)=k1_wellord1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1159, c_58])).
% 6.38/2.43  tff(c_1343, plain, (![B_189]: (k1_wellord1(k1_xboole_0, B_189)=k1_wellord1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1191])).
% 6.38/2.43  tff(c_1398, plain, (![D_143]: (~r2_hidden(D_143, k1_wellord1('#skF_6', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_1343, c_793])).
% 6.38/2.43  tff(c_5703, plain, (![C_4799, B_4800, A_4801]: (~r1_tarski(C_4799, k1_wellord1('#skF_6', '#skF_5')) | r2_hidden(B_4800, k3_relat_1(A_4801)) | k1_wellord1(A_4801, B_4800)=C_4799 | ~v1_relat_1(A_4801))), inference(resolution, [status(thm)], [c_5661, c_1398])).
% 6.38/2.43  tff(c_5768, plain, (![B_4802, A_4803]: (r2_hidden(B_4802, k3_relat_1(A_4803)) | k1_wellord1(A_4803, B_4802)=k1_xboole_0 | ~v1_relat_1(A_4803))), inference(resolution, [status(thm)], [c_185, c_5703])).
% 6.38/2.43  tff(c_5803, plain, (k1_wellord1('#skF_6', '#skF_5')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_5768, c_58])).
% 6.38/2.43  tff(c_5815, plain, (k1_wellord1('#skF_6', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60, c_5803])).
% 6.38/2.43  tff(c_5817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_5815])).
% 6.38/2.43  tff(c_5818, plain, (![A_18]: (~v1_relat_1(A_18))), inference(splitRight, [status(thm)], [c_792])).
% 6.38/2.43  tff(c_5823, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5818, c_97])).
% 6.38/2.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.38/2.43  
% 6.38/2.43  Inference rules
% 6.38/2.43  ----------------------
% 6.38/2.43  #Ref     : 2
% 6.38/2.43  #Sup     : 1257
% 6.38/2.43  #Fact    : 6
% 6.38/2.43  #Define  : 0
% 6.38/2.43  #Split   : 10
% 6.38/2.43  #Chain   : 0
% 6.38/2.43  #Close   : 0
% 6.38/2.43  
% 6.38/2.43  Ordering : KBO
% 6.38/2.43  
% 6.38/2.43  Simplification rules
% 6.38/2.43  ----------------------
% 6.38/2.43  #Subsume      : 533
% 6.38/2.43  #Demod        : 422
% 6.38/2.43  #Tautology    : 231
% 6.38/2.43  #SimpNegUnit  : 134
% 6.38/2.43  #BackRed      : 53
% 6.38/2.43  
% 6.38/2.43  #Partial instantiations: 460
% 6.38/2.43  #Strategies tried      : 1
% 6.38/2.43  
% 6.38/2.43  Timing (in seconds)
% 6.38/2.43  ----------------------
% 6.38/2.43  Preprocessing        : 0.30
% 6.38/2.43  Parsing              : 0.15
% 6.38/2.43  CNF conversion       : 0.02
% 6.38/2.43  Main loop            : 1.22
% 6.38/2.43  Inferencing          : 0.43
% 6.38/2.43  Reduction            : 0.33
% 6.38/2.43  Demodulation         : 0.21
% 6.38/2.43  BG Simplification    : 0.05
% 6.38/2.43  Subsumption          : 0.32
% 6.38/2.43  Abstraction          : 0.06
% 6.38/2.43  MUC search           : 0.00
% 6.38/2.43  Cooper               : 0.00
% 6.38/2.43  Total                : 1.55
% 6.38/2.43  Index Insertion      : 0.00
% 6.38/2.43  Index Deletion       : 0.00
% 6.38/2.43  Index Matching       : 0.00
% 6.38/2.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
