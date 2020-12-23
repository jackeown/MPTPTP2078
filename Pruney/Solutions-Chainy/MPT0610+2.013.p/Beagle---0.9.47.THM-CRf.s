%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:38 EST 2020

% Result     : Theorem 4.33s
% Output     : CNFRefutation 4.43s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 139 expanded)
%              Number of leaves         :   28 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  105 ( 304 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_73,plain,(
    ! [A_39,B_40] :
      ( r1_xboole_0(A_39,B_40)
      | k3_xboole_0(A_39,B_40) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_80,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73,c_42])).

tff(c_48,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_46,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_44,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_94,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = k1_xboole_0
      | ~ r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_106,plain,(
    k3_xboole_0(k1_relat_1('#skF_3'),k1_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_94])).

tff(c_573,plain,(
    ! [A_99,B_100] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_99,B_100)),k3_xboole_0(k1_relat_1(A_99),k1_relat_1(B_100)))
      | ~ v1_relat_1(B_100)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_611,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0('#skF_3','#skF_4')),k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_573])).

tff(c_615,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0('#skF_3','#skF_4')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_611])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,(
    ! [B_36,A_37] :
      ( r1_xboole_0(B_36,A_37)
      | ~ r1_xboole_0(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_53,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_50])).

tff(c_174,plain,(
    ! [B_60,A_61] :
      ( k9_relat_1(B_60,A_61) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_60),A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_185,plain,
    ( k9_relat_1('#skF_4',k1_relat_1('#skF_3')) = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_53,c_174])).

tff(c_193,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_185])).

tff(c_1107,plain,(
    ! [A_129,B_130,C_131] :
      ( r2_hidden('#skF_2'(A_129,B_130,C_131),k1_relat_1(C_131))
      | ~ r2_hidden(A_129,k9_relat_1(C_131,B_130))
      | ~ v1_relat_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_416,plain,(
    ! [A_82,B_83,C_84] :
      ( r2_hidden('#skF_2'(A_82,B_83,C_84),B_83)
      | ~ r2_hidden(A_82,k9_relat_1(C_84,B_83))
      | ~ v1_relat_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_150,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,B_57)
      | ~ r2_hidden(C_58,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_162,plain,(
    ! [C_58] :
      ( ~ r2_hidden(C_58,k1_relat_1('#skF_4'))
      | ~ r2_hidden(C_58,k1_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_44,c_150])).

tff(c_427,plain,(
    ! [A_82,C_84] :
      ( ~ r2_hidden('#skF_2'(A_82,k1_relat_1('#skF_3'),C_84),k1_relat_1('#skF_4'))
      | ~ r2_hidden(A_82,k9_relat_1(C_84,k1_relat_1('#skF_3')))
      | ~ v1_relat_1(C_84) ) ),
    inference(resolution,[status(thm)],[c_416,c_162])).

tff(c_1111,plain,(
    ! [A_129] :
      ( ~ r2_hidden(A_129,k9_relat_1('#skF_4',k1_relat_1('#skF_3')))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1107,c_427])).

tff(c_1134,plain,(
    ! [A_132] : ~ r2_hidden(A_132,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_193,c_1111])).

tff(c_1150,plain,(
    ! [A_133] : r1_xboole_0(A_133,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_1134])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( k1_xboole_0 = A_10
      | ~ r1_xboole_0(B_11,C_12)
      | ~ r1_tarski(A_10,C_12)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1869,plain,(
    ! [A_168,A_169] :
      ( k1_xboole_0 = A_168
      | ~ r1_tarski(A_168,k1_xboole_0)
      | ~ r1_tarski(A_168,A_169) ) ),
    inference(resolution,[status(thm)],[c_1150,c_14])).

tff(c_1882,plain,(
    ! [A_169] :
      ( k1_relat_1(k3_xboole_0('#skF_3','#skF_4')) = k1_xboole_0
      | ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_3','#skF_4')),A_169) ) ),
    inference(resolution,[status(thm)],[c_615,c_1869])).

tff(c_2110,plain,(
    ! [A_169] : ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_3','#skF_4')),A_169) ),
    inference(splitLeft,[status(thm)],[c_1882])).

tff(c_2112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2110,c_615])).

tff(c_2113,plain,(
    k1_relat_1(k3_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1882])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k3_xboole_0(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_58,plain,(
    ! [A_38] :
      ( k1_relat_1(A_38) != k1_xboole_0
      | k1_xboole_0 = A_38
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_68,plain,(
    ! [A_13,B_14] :
      ( k1_relat_1(k3_xboole_0(A_13,B_14)) != k1_xboole_0
      | k3_xboole_0(A_13,B_14) = k1_xboole_0
      | ~ v1_relat_1(A_13) ) ),
    inference(resolution,[status(thm)],[c_16,c_58])).

tff(c_2139,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2113,c_68])).

tff(c_2175,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2139])).

tff(c_2177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:24:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.33/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.33/1.83  
% 4.33/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.33/1.83  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 4.33/1.83  
% 4.33/1.83  %Foreground sorts:
% 4.33/1.83  
% 4.33/1.83  
% 4.33/1.83  %Background operators:
% 4.33/1.83  
% 4.33/1.83  
% 4.33/1.83  %Foreground operators:
% 4.33/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.33/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.33/1.83  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.33/1.83  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.33/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.33/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.33/1.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.33/1.83  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.33/1.83  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.33/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.33/1.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.33/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.33/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.33/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.33/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.33/1.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.33/1.83  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.33/1.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.33/1.83  
% 4.43/1.84  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.43/1.84  tff(f_117, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t214_relat_1)).
% 4.43/1.84  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relat_1)).
% 4.43/1.84  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.43/1.84  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.43/1.84  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 4.43/1.84  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 4.43/1.84  tff(f_59, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 4.43/1.84  tff(f_63, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 4.43/1.84  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.43/1.84  tff(c_73, plain, (![A_39, B_40]: (r1_xboole_0(A_39, B_40) | k3_xboole_0(A_39, B_40)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.43/1.84  tff(c_42, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.43/1.84  tff(c_80, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_73, c_42])).
% 4.43/1.84  tff(c_48, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.43/1.84  tff(c_46, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.43/1.84  tff(c_44, plain, (r1_xboole_0(k1_relat_1('#skF_3'), k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.43/1.84  tff(c_94, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=k1_xboole_0 | ~r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.43/1.84  tff(c_106, plain, (k3_xboole_0(k1_relat_1('#skF_3'), k1_relat_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_94])).
% 4.43/1.84  tff(c_573, plain, (![A_99, B_100]: (r1_tarski(k1_relat_1(k3_xboole_0(A_99, B_100)), k3_xboole_0(k1_relat_1(A_99), k1_relat_1(B_100))) | ~v1_relat_1(B_100) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.43/1.84  tff(c_611, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k1_xboole_0) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_106, c_573])).
% 4.43/1.84  tff(c_615, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_611])).
% 4.43/1.84  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.43/1.84  tff(c_50, plain, (![B_36, A_37]: (r1_xboole_0(B_36, A_37) | ~r1_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.43/1.84  tff(c_53, plain, (r1_xboole_0(k1_relat_1('#skF_4'), k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_50])).
% 4.43/1.84  tff(c_174, plain, (![B_60, A_61]: (k9_relat_1(B_60, A_61)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_60), A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.43/1.84  tff(c_185, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_3'))=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_53, c_174])).
% 4.43/1.84  tff(c_193, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_185])).
% 4.43/1.84  tff(c_1107, plain, (![A_129, B_130, C_131]: (r2_hidden('#skF_2'(A_129, B_130, C_131), k1_relat_1(C_131)) | ~r2_hidden(A_129, k9_relat_1(C_131, B_130)) | ~v1_relat_1(C_131))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.43/1.84  tff(c_416, plain, (![A_82, B_83, C_84]: (r2_hidden('#skF_2'(A_82, B_83, C_84), B_83) | ~r2_hidden(A_82, k9_relat_1(C_84, B_83)) | ~v1_relat_1(C_84))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.43/1.84  tff(c_150, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, B_57) | ~r2_hidden(C_58, A_56))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.43/1.84  tff(c_162, plain, (![C_58]: (~r2_hidden(C_58, k1_relat_1('#skF_4')) | ~r2_hidden(C_58, k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_44, c_150])).
% 4.43/1.84  tff(c_427, plain, (![A_82, C_84]: (~r2_hidden('#skF_2'(A_82, k1_relat_1('#skF_3'), C_84), k1_relat_1('#skF_4')) | ~r2_hidden(A_82, k9_relat_1(C_84, k1_relat_1('#skF_3'))) | ~v1_relat_1(C_84))), inference(resolution, [status(thm)], [c_416, c_162])).
% 4.43/1.84  tff(c_1111, plain, (![A_129]: (~r2_hidden(A_129, k9_relat_1('#skF_4', k1_relat_1('#skF_3'))) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1107, c_427])).
% 4.43/1.84  tff(c_1134, plain, (![A_132]: (~r2_hidden(A_132, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_193, c_1111])).
% 4.43/1.84  tff(c_1150, plain, (![A_133]: (r1_xboole_0(A_133, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_1134])).
% 4.43/1.84  tff(c_14, plain, (![A_10, B_11, C_12]: (k1_xboole_0=A_10 | ~r1_xboole_0(B_11, C_12) | ~r1_tarski(A_10, C_12) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.43/1.84  tff(c_1869, plain, (![A_168, A_169]: (k1_xboole_0=A_168 | ~r1_tarski(A_168, k1_xboole_0) | ~r1_tarski(A_168, A_169))), inference(resolution, [status(thm)], [c_1150, c_14])).
% 4.43/1.84  tff(c_1882, plain, (![A_169]: (k1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0 | ~r1_tarski(k1_relat_1(k3_xboole_0('#skF_3', '#skF_4')), A_169))), inference(resolution, [status(thm)], [c_615, c_1869])).
% 4.43/1.84  tff(c_2110, plain, (![A_169]: (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_3', '#skF_4')), A_169))), inference(splitLeft, [status(thm)], [c_1882])).
% 4.43/1.84  tff(c_2112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2110, c_615])).
% 4.43/1.84  tff(c_2113, plain, (k1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1882])).
% 4.43/1.84  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k3_xboole_0(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.43/1.84  tff(c_58, plain, (![A_38]: (k1_relat_1(A_38)!=k1_xboole_0 | k1_xboole_0=A_38 | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.43/1.84  tff(c_68, plain, (![A_13, B_14]: (k1_relat_1(k3_xboole_0(A_13, B_14))!=k1_xboole_0 | k3_xboole_0(A_13, B_14)=k1_xboole_0 | ~v1_relat_1(A_13))), inference(resolution, [status(thm)], [c_16, c_58])).
% 4.43/1.84  tff(c_2139, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2113, c_68])).
% 4.43/1.84  tff(c_2175, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2139])).
% 4.43/1.84  tff(c_2177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_2175])).
% 4.43/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.85  
% 4.43/1.85  Inference rules
% 4.43/1.85  ----------------------
% 4.43/1.85  #Ref     : 0
% 4.43/1.85  #Sup     : 517
% 4.43/1.85  #Fact    : 0
% 4.43/1.85  #Define  : 0
% 4.43/1.85  #Split   : 11
% 4.43/1.85  #Chain   : 0
% 4.43/1.85  #Close   : 0
% 4.43/1.85  
% 4.43/1.85  Ordering : KBO
% 4.43/1.85  
% 4.43/1.85  Simplification rules
% 4.43/1.85  ----------------------
% 4.43/1.85  #Subsume      : 96
% 4.43/1.85  #Demod        : 211
% 4.43/1.85  #Tautology    : 196
% 4.43/1.85  #SimpNegUnit  : 9
% 4.43/1.85  #BackRed      : 4
% 4.43/1.85  
% 4.43/1.85  #Partial instantiations: 0
% 4.43/1.85  #Strategies tried      : 1
% 4.43/1.85  
% 4.43/1.85  Timing (in seconds)
% 4.43/1.85  ----------------------
% 4.43/1.85  Preprocessing        : 0.35
% 4.43/1.85  Parsing              : 0.19
% 4.43/1.85  CNF conversion       : 0.02
% 4.43/1.85  Main loop            : 0.71
% 4.43/1.85  Inferencing          : 0.25
% 4.43/1.85  Reduction            : 0.22
% 4.43/1.85  Demodulation         : 0.15
% 4.43/1.85  BG Simplification    : 0.03
% 4.43/1.85  Subsumption          : 0.14
% 4.43/1.85  Abstraction          : 0.04
% 4.43/1.85  MUC search           : 0.00
% 4.43/1.85  Cooper               : 0.00
% 4.43/1.85  Total                : 1.10
% 4.43/1.85  Index Insertion      : 0.00
% 4.43/1.85  Index Deletion       : 0.00
% 4.43/1.85  Index Matching       : 0.00
% 4.43/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
