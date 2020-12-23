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
% DateTime   : Thu Dec  3 10:02:38 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   59 (  76 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   97 ( 159 expanded)
%              Number of equality atoms :   30 (  31 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_133,plain,(
    ! [A_35,B_36,C_37] :
      ( ~ r1_xboole_0(A_35,B_36)
      | ~ r2_hidden(C_37,B_36)
      | ~ r2_hidden(C_37,A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_158,plain,(
    ! [C_40,B_41,A_42] :
      ( ~ r2_hidden(C_40,B_41)
      | ~ r2_hidden(C_40,A_42)
      | k3_xboole_0(A_42,B_41) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_133])).

tff(c_286,plain,(
    ! [A_50,B_51,A_52] :
      ( ~ r2_hidden('#skF_1'(A_50,B_51),A_52)
      | k3_xboole_0(A_52,A_50) != k1_xboole_0
      | r1_xboole_0(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_10,c_158])).

tff(c_296,plain,(
    ! [B_55,A_56] :
      ( k3_xboole_0(B_55,A_56) != k1_xboole_0
      | r1_xboole_0(A_56,B_55) ) ),
    inference(resolution,[status(thm)],[c_8,c_286])).

tff(c_26,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_307,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_296,c_26])).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_140,plain,(
    ! [C_38] :
      ( ~ r2_hidden(C_38,k1_relat_1('#skF_3'))
      | ~ r2_hidden(C_38,k1_relat_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_28,c_133])).

tff(c_165,plain,(
    ! [A_43] :
      ( ~ r2_hidden('#skF_1'(A_43,k1_relat_1('#skF_2')),k1_relat_1('#skF_3'))
      | r1_xboole_0(A_43,k1_relat_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_8,c_140])).

tff(c_170,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_165])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_177,plain,(
    k3_xboole_0(k1_relat_1('#skF_3'),k1_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_170,c_2])).

tff(c_189,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_44,B_45)),k3_xboole_0(k1_relat_1(A_44),k1_relat_1(B_45)))
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_195,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0('#skF_3','#skF_2')),k1_xboole_0)
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_189])).

tff(c_203,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0('#skF_3','#skF_2')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_195])).

tff(c_12,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_235,plain,(
    k1_relat_1(k3_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_203,c_12])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k3_xboole_0(A_9,B_10))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_103,plain,(
    ! [A_30] :
      ( k2_relat_1(A_30) = k1_xboole_0
      | k1_relat_1(A_30) != k1_xboole_0
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_262,plain,(
    ! [A_48,B_49] :
      ( k2_relat_1(k3_xboole_0(A_48,B_49)) = k1_xboole_0
      | k1_relat_1(k3_xboole_0(A_48,B_49)) != k1_xboole_0
      | ~ v1_relat_1(A_48) ) ),
    inference(resolution,[status(thm)],[c_14,c_103])).

tff(c_16,plain,(
    ! [A_11] :
      ( k8_relat_1(k2_relat_1(A_11),A_11) = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_343,plain,(
    ! [A_70,B_71] :
      ( k8_relat_1(k1_xboole_0,k3_xboole_0(A_70,B_71)) = k3_xboole_0(A_70,B_71)
      | ~ v1_relat_1(k3_xboole_0(A_70,B_71))
      | k1_relat_1(k3_xboole_0(A_70,B_71)) != k1_xboole_0
      | ~ v1_relat_1(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_16])).

tff(c_365,plain,(
    ! [A_75,B_76] :
      ( k8_relat_1(k1_xboole_0,k3_xboole_0(A_75,B_76)) = k3_xboole_0(A_75,B_76)
      | k1_relat_1(k3_xboole_0(A_75,B_76)) != k1_xboole_0
      | ~ v1_relat_1(A_75) ) ),
    inference(resolution,[status(thm)],[c_14,c_343])).

tff(c_51,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k3_xboole_0(A_20,B_21))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_12] :
      ( k8_relat_1(k1_xboole_0,A_12) = k1_xboole_0
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_55,plain,(
    ! [A_20,B_21] :
      ( k8_relat_1(k1_xboole_0,k3_xboole_0(A_20,B_21)) = k1_xboole_0
      | ~ v1_relat_1(A_20) ) ),
    inference(resolution,[status(thm)],[c_51,c_18])).

tff(c_388,plain,(
    ! [A_77,B_78] :
      ( k3_xboole_0(A_77,B_78) = k1_xboole_0
      | ~ v1_relat_1(A_77)
      | k1_relat_1(k3_xboole_0(A_77,B_78)) != k1_xboole_0
      | ~ v1_relat_1(A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_55])).

tff(c_391,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_388])).

tff(c_403,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_391])).

tff(c_405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_403])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:48:21 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.30  
% 2.19/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.31  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.19/1.31  
% 2.19/1.31  %Foreground sorts:
% 2.19/1.31  
% 2.19/1.31  
% 2.19/1.31  %Background operators:
% 2.19/1.31  
% 2.19/1.31  
% 2.19/1.31  %Foreground operators:
% 2.19/1.31  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.19/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.19/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.19/1.31  
% 2.19/1.32  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.19/1.32  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.19/1.32  tff(f_86, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t214_relat_1)).
% 2.19/1.32  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relat_1)).
% 2.19/1.32  tff(f_51, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.19/1.32  tff(f_55, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.19/1.32  tff(f_76, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.19/1.32  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_relat_1)).
% 2.19/1.32  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 2.19/1.32  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.19/1.32  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.19/1.32  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.19/1.32  tff(c_133, plain, (![A_35, B_36, C_37]: (~r1_xboole_0(A_35, B_36) | ~r2_hidden(C_37, B_36) | ~r2_hidden(C_37, A_35))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.19/1.32  tff(c_158, plain, (![C_40, B_41, A_42]: (~r2_hidden(C_40, B_41) | ~r2_hidden(C_40, A_42) | k3_xboole_0(A_42, B_41)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_133])).
% 2.19/1.32  tff(c_286, plain, (![A_50, B_51, A_52]: (~r2_hidden('#skF_1'(A_50, B_51), A_52) | k3_xboole_0(A_52, A_50)!=k1_xboole_0 | r1_xboole_0(A_50, B_51))), inference(resolution, [status(thm)], [c_10, c_158])).
% 2.19/1.32  tff(c_296, plain, (![B_55, A_56]: (k3_xboole_0(B_55, A_56)!=k1_xboole_0 | r1_xboole_0(A_56, B_55))), inference(resolution, [status(thm)], [c_8, c_286])).
% 2.19/1.32  tff(c_26, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.19/1.32  tff(c_307, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_296, c_26])).
% 2.19/1.32  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.19/1.32  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.19/1.32  tff(c_28, plain, (r1_xboole_0(k1_relat_1('#skF_2'), k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.19/1.32  tff(c_140, plain, (![C_38]: (~r2_hidden(C_38, k1_relat_1('#skF_3')) | ~r2_hidden(C_38, k1_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_28, c_133])).
% 2.19/1.32  tff(c_165, plain, (![A_43]: (~r2_hidden('#skF_1'(A_43, k1_relat_1('#skF_2')), k1_relat_1('#skF_3')) | r1_xboole_0(A_43, k1_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_140])).
% 2.19/1.32  tff(c_170, plain, (r1_xboole_0(k1_relat_1('#skF_3'), k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_165])).
% 2.19/1.32  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.19/1.32  tff(c_177, plain, (k3_xboole_0(k1_relat_1('#skF_3'), k1_relat_1('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_170, c_2])).
% 2.19/1.32  tff(c_189, plain, (![A_44, B_45]: (r1_tarski(k1_relat_1(k3_xboole_0(A_44, B_45)), k3_xboole_0(k1_relat_1(A_44), k1_relat_1(B_45))) | ~v1_relat_1(B_45) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.19/1.32  tff(c_195, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_3', '#skF_2')), k1_xboole_0) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_177, c_189])).
% 2.19/1.32  tff(c_203, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_3', '#skF_2')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_195])).
% 2.19/1.32  tff(c_12, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.19/1.32  tff(c_235, plain, (k1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_203, c_12])).
% 2.19/1.32  tff(c_14, plain, (![A_9, B_10]: (v1_relat_1(k3_xboole_0(A_9, B_10)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.19/1.32  tff(c_103, plain, (![A_30]: (k2_relat_1(A_30)=k1_xboole_0 | k1_relat_1(A_30)!=k1_xboole_0 | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.19/1.32  tff(c_262, plain, (![A_48, B_49]: (k2_relat_1(k3_xboole_0(A_48, B_49))=k1_xboole_0 | k1_relat_1(k3_xboole_0(A_48, B_49))!=k1_xboole_0 | ~v1_relat_1(A_48))), inference(resolution, [status(thm)], [c_14, c_103])).
% 2.19/1.32  tff(c_16, plain, (![A_11]: (k8_relat_1(k2_relat_1(A_11), A_11)=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.19/1.32  tff(c_343, plain, (![A_70, B_71]: (k8_relat_1(k1_xboole_0, k3_xboole_0(A_70, B_71))=k3_xboole_0(A_70, B_71) | ~v1_relat_1(k3_xboole_0(A_70, B_71)) | k1_relat_1(k3_xboole_0(A_70, B_71))!=k1_xboole_0 | ~v1_relat_1(A_70))), inference(superposition, [status(thm), theory('equality')], [c_262, c_16])).
% 2.19/1.32  tff(c_365, plain, (![A_75, B_76]: (k8_relat_1(k1_xboole_0, k3_xboole_0(A_75, B_76))=k3_xboole_0(A_75, B_76) | k1_relat_1(k3_xboole_0(A_75, B_76))!=k1_xboole_0 | ~v1_relat_1(A_75))), inference(resolution, [status(thm)], [c_14, c_343])).
% 2.19/1.32  tff(c_51, plain, (![A_20, B_21]: (v1_relat_1(k3_xboole_0(A_20, B_21)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.19/1.32  tff(c_18, plain, (![A_12]: (k8_relat_1(k1_xboole_0, A_12)=k1_xboole_0 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.19/1.32  tff(c_55, plain, (![A_20, B_21]: (k8_relat_1(k1_xboole_0, k3_xboole_0(A_20, B_21))=k1_xboole_0 | ~v1_relat_1(A_20))), inference(resolution, [status(thm)], [c_51, c_18])).
% 2.19/1.32  tff(c_388, plain, (![A_77, B_78]: (k3_xboole_0(A_77, B_78)=k1_xboole_0 | ~v1_relat_1(A_77) | k1_relat_1(k3_xboole_0(A_77, B_78))!=k1_xboole_0 | ~v1_relat_1(A_77))), inference(superposition, [status(thm), theory('equality')], [c_365, c_55])).
% 2.19/1.32  tff(c_391, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_235, c_388])).
% 2.19/1.32  tff(c_403, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_391])).
% 2.19/1.32  tff(c_405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_307, c_403])).
% 2.19/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.32  
% 2.19/1.32  Inference rules
% 2.19/1.32  ----------------------
% 2.19/1.32  #Ref     : 0
% 2.19/1.32  #Sup     : 91
% 2.19/1.32  #Fact    : 0
% 2.19/1.32  #Define  : 0
% 2.19/1.32  #Split   : 4
% 2.19/1.32  #Chain   : 0
% 2.19/1.32  #Close   : 0
% 2.19/1.32  
% 2.19/1.32  Ordering : KBO
% 2.19/1.32  
% 2.19/1.32  Simplification rules
% 2.19/1.32  ----------------------
% 2.19/1.32  #Subsume      : 19
% 2.19/1.32  #Demod        : 33
% 2.19/1.32  #Tautology    : 29
% 2.19/1.32  #SimpNegUnit  : 3
% 2.19/1.32  #BackRed      : 2
% 2.19/1.32  
% 2.19/1.32  #Partial instantiations: 0
% 2.19/1.32  #Strategies tried      : 1
% 2.19/1.32  
% 2.19/1.32  Timing (in seconds)
% 2.19/1.32  ----------------------
% 2.19/1.32  Preprocessing        : 0.27
% 2.19/1.32  Parsing              : 0.15
% 2.19/1.32  CNF conversion       : 0.02
% 2.19/1.32  Main loop            : 0.27
% 2.19/1.32  Inferencing          : 0.11
% 2.19/1.32  Reduction            : 0.07
% 2.19/1.32  Demodulation         : 0.04
% 2.19/1.32  BG Simplification    : 0.01
% 2.19/1.32  Subsumption          : 0.06
% 2.19/1.32  Abstraction          : 0.01
% 2.19/1.32  MUC search           : 0.00
% 2.19/1.32  Cooper               : 0.00
% 2.19/1.32  Total                : 0.57
% 2.19/1.32  Index Insertion      : 0.00
% 2.19/1.32  Index Deletion       : 0.00
% 2.19/1.32  Index Matching       : 0.00
% 2.19/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
