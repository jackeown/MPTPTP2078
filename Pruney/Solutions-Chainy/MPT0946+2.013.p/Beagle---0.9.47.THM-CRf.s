%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:33 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 225 expanded)
%              Number of leaves         :   31 (  93 expanded)
%              Depth                    :   15
%              Number of atoms          :  149 ( 517 expanded)
%              Number of equality atoms :   16 (  76 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_101,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_48,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_88,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_97,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_wellord1(B,A),k3_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_50,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_42,plain,(
    ! [A_28] :
      ( v2_wellord1(k1_wellord2(A_28))
      | ~ v3_ordinal1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_52,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_46,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( r2_hidden(B_7,A_5)
      | r1_ordinal1(A_5,B_7)
      | ~ v3_ordinal1(B_7)
      | ~ v3_ordinal1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_38,plain,(
    ! [A_24] : v1_relat_1(k1_wellord2(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_48,plain,(
    r4_wellord1(k1_wellord2('#skF_3'),k1_wellord2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_123,plain,(
    ! [B_50,A_51] :
      ( r4_wellord1(B_50,A_51)
      | ~ r4_wellord1(A_51,B_50)
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_125,plain,
    ( r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3'))
    | ~ v1_relat_1(k1_wellord2('#skF_4'))
    | ~ v1_relat_1(k1_wellord2('#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_123])).

tff(c_128,plain,(
    r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_125])).

tff(c_40,plain,(
    ! [B_27,A_25] :
      ( k1_wellord1(k1_wellord2(B_27),A_25) = A_25
      | ~ r2_hidden(A_25,B_27)
      | ~ v3_ordinal1(B_27)
      | ~ v3_ordinal1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,(
    ! [A_16] :
      ( k3_relat_1(k1_wellord2(A_16)) = A_16
      | ~ v1_relat_1(k1_wellord2(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_58,plain,(
    ! [A_16] : k3_relat_1(k1_wellord2(A_16)) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32])).

tff(c_72,plain,(
    ! [B_36,A_37] :
      ( r1_tarski(k1_wellord1(B_36,A_37),k3_relat_1(B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_75,plain,(
    ! [A_16,A_37] :
      ( r1_tarski(k1_wellord1(k1_wellord2(A_16),A_37),A_16)
      | ~ v1_relat_1(k1_wellord2(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_72])).

tff(c_77,plain,(
    ! [A_16,A_37] : r1_tarski(k1_wellord1(k1_wellord2(A_16),A_37),A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_75])).

tff(c_44,plain,(
    ! [B_30,A_29] :
      ( k2_wellord1(k1_wellord2(B_30),A_29) = k1_wellord2(A_29)
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_276,plain,(
    ! [A_71,B_72] :
      ( ~ r4_wellord1(A_71,k2_wellord1(A_71,k1_wellord1(A_71,B_72)))
      | ~ r2_hidden(B_72,k3_relat_1(A_71))
      | ~ v2_wellord1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_283,plain,(
    ! [B_30,B_72] :
      ( ~ r4_wellord1(k1_wellord2(B_30),k1_wellord2(k1_wellord1(k1_wellord2(B_30),B_72)))
      | ~ r2_hidden(B_72,k3_relat_1(k1_wellord2(B_30)))
      | ~ v2_wellord1(k1_wellord2(B_30))
      | ~ v1_relat_1(k1_wellord2(B_30))
      | ~ r1_tarski(k1_wellord1(k1_wellord2(B_30),B_72),B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_276])).

tff(c_295,plain,(
    ! [B_75,B_76] :
      ( ~ r4_wellord1(k1_wellord2(B_75),k1_wellord2(k1_wellord1(k1_wellord2(B_75),B_76)))
      | ~ r2_hidden(B_76,B_75)
      | ~ v2_wellord1(k1_wellord2(B_75)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_38,c_58,c_283])).

tff(c_448,plain,(
    ! [B_95,A_96] :
      ( ~ r4_wellord1(k1_wellord2(B_95),k1_wellord2(A_96))
      | ~ r2_hidden(A_96,B_95)
      | ~ v2_wellord1(k1_wellord2(B_95))
      | ~ r2_hidden(A_96,B_95)
      | ~ v3_ordinal1(B_95)
      | ~ v3_ordinal1(A_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_295])).

tff(c_451,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_128,c_448])).

tff(c_457,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_451])).

tff(c_461,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_457])).

tff(c_468,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_461])).

tff(c_471,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_468])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_ordinal1(A_3,B_4)
      | ~ v3_ordinal1(B_4)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_102,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ r1_ordinal1(A_46,B_47)
      | ~ v3_ordinal1(B_47)
      | ~ v3_ordinal1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_194,plain,(
    ! [B_63,A_64] :
      ( B_63 = A_64
      | ~ r1_tarski(B_63,A_64)
      | ~ r1_ordinal1(A_64,B_63)
      | ~ v3_ordinal1(B_63)
      | ~ v3_ordinal1(A_64) ) ),
    inference(resolution,[status(thm)],[c_102,c_2])).

tff(c_211,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_ordinal1(B_4,A_3)
      | ~ r1_ordinal1(A_3,B_4)
      | ~ v3_ordinal1(B_4)
      | ~ v3_ordinal1(A_3) ) ),
    inference(resolution,[status(thm)],[c_10,c_194])).

tff(c_473,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_471,c_211])).

tff(c_476,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_473])).

tff(c_477,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_476])).

tff(c_454,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_448])).

tff(c_460,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_454])).

tff(c_490,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_460])).

tff(c_493,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_490])).

tff(c_496,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_493])).

tff(c_498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_477,c_496])).

tff(c_499,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_460])).

tff(c_503,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_499])).

tff(c_507,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_503])).

tff(c_508,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_457])).

tff(c_512,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_508])).

tff(c_516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:34:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.41  
% 2.66/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.41  %$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.66/1.41  
% 2.66/1.41  %Foreground sorts:
% 2.66/1.41  
% 2.66/1.41  
% 2.66/1.41  %Background operators:
% 2.66/1.41  
% 2.66/1.41  
% 2.66/1.41  %Foreground operators:
% 2.66/1.41  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.66/1.41  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.66/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.41  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.66/1.41  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.66/1.41  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.66/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.41  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.41  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.66/1.41  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.66/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.66/1.41  
% 3.01/1.43  tff(f_115, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_wellord2)).
% 3.01/1.43  tff(f_101, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_wellord2)).
% 3.01/1.43  tff(f_48, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 3.01/1.43  tff(f_88, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.01/1.43  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 3.01/1.43  tff(f_97, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord2)).
% 3.01/1.43  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 3.01/1.43  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_wellord1(B, A), k3_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_wellord1)).
% 3.01/1.43  tff(f_105, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 3.01/1.43  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_wellord1)).
% 3.01/1.43  tff(f_39, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.01/1.43  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.01/1.43  tff(c_50, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.01/1.43  tff(c_42, plain, (![A_28]: (v2_wellord1(k1_wellord2(A_28)) | ~v3_ordinal1(A_28))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.01/1.43  tff(c_52, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.01/1.43  tff(c_46, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.01/1.43  tff(c_12, plain, (![B_7, A_5]: (r2_hidden(B_7, A_5) | r1_ordinal1(A_5, B_7) | ~v3_ordinal1(B_7) | ~v3_ordinal1(A_5))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.01/1.43  tff(c_38, plain, (![A_24]: (v1_relat_1(k1_wellord2(A_24)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.01/1.43  tff(c_48, plain, (r4_wellord1(k1_wellord2('#skF_3'), k1_wellord2('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.01/1.43  tff(c_123, plain, (![B_50, A_51]: (r4_wellord1(B_50, A_51) | ~r4_wellord1(A_51, B_50) | ~v1_relat_1(B_50) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.01/1.43  tff(c_125, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3')) | ~v1_relat_1(k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_123])).
% 3.01/1.43  tff(c_128, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_125])).
% 3.01/1.43  tff(c_40, plain, (![B_27, A_25]: (k1_wellord1(k1_wellord2(B_27), A_25)=A_25 | ~r2_hidden(A_25, B_27) | ~v3_ordinal1(B_27) | ~v3_ordinal1(A_25))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.01/1.43  tff(c_32, plain, (![A_16]: (k3_relat_1(k1_wellord2(A_16))=A_16 | ~v1_relat_1(k1_wellord2(A_16)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.01/1.43  tff(c_58, plain, (![A_16]: (k3_relat_1(k1_wellord2(A_16))=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32])).
% 3.01/1.43  tff(c_72, plain, (![B_36, A_37]: (r1_tarski(k1_wellord1(B_36, A_37), k3_relat_1(B_36)) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.01/1.43  tff(c_75, plain, (![A_16, A_37]: (r1_tarski(k1_wellord1(k1_wellord2(A_16), A_37), A_16) | ~v1_relat_1(k1_wellord2(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_72])).
% 3.01/1.43  tff(c_77, plain, (![A_16, A_37]: (r1_tarski(k1_wellord1(k1_wellord2(A_16), A_37), A_16))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_75])).
% 3.01/1.43  tff(c_44, plain, (![B_30, A_29]: (k2_wellord1(k1_wellord2(B_30), A_29)=k1_wellord2(A_29) | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.01/1.43  tff(c_276, plain, (![A_71, B_72]: (~r4_wellord1(A_71, k2_wellord1(A_71, k1_wellord1(A_71, B_72))) | ~r2_hidden(B_72, k3_relat_1(A_71)) | ~v2_wellord1(A_71) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.01/1.43  tff(c_283, plain, (![B_30, B_72]: (~r4_wellord1(k1_wellord2(B_30), k1_wellord2(k1_wellord1(k1_wellord2(B_30), B_72))) | ~r2_hidden(B_72, k3_relat_1(k1_wellord2(B_30))) | ~v2_wellord1(k1_wellord2(B_30)) | ~v1_relat_1(k1_wellord2(B_30)) | ~r1_tarski(k1_wellord1(k1_wellord2(B_30), B_72), B_30))), inference(superposition, [status(thm), theory('equality')], [c_44, c_276])).
% 3.01/1.43  tff(c_295, plain, (![B_75, B_76]: (~r4_wellord1(k1_wellord2(B_75), k1_wellord2(k1_wellord1(k1_wellord2(B_75), B_76))) | ~r2_hidden(B_76, B_75) | ~v2_wellord1(k1_wellord2(B_75)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_38, c_58, c_283])).
% 3.01/1.43  tff(c_448, plain, (![B_95, A_96]: (~r4_wellord1(k1_wellord2(B_95), k1_wellord2(A_96)) | ~r2_hidden(A_96, B_95) | ~v2_wellord1(k1_wellord2(B_95)) | ~r2_hidden(A_96, B_95) | ~v3_ordinal1(B_95) | ~v3_ordinal1(A_96))), inference(superposition, [status(thm), theory('equality')], [c_40, c_295])).
% 3.01/1.43  tff(c_451, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_128, c_448])).
% 3.01/1.43  tff(c_457, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_451])).
% 3.01/1.43  tff(c_461, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_457])).
% 3.01/1.43  tff(c_468, plain, (r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_461])).
% 3.01/1.43  tff(c_471, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_468])).
% 3.01/1.43  tff(c_10, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~r1_ordinal1(A_3, B_4) | ~v3_ordinal1(B_4) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.01/1.43  tff(c_102, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~r1_ordinal1(A_46, B_47) | ~v3_ordinal1(B_47) | ~v3_ordinal1(A_46))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.01/1.43  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.01/1.43  tff(c_194, plain, (![B_63, A_64]: (B_63=A_64 | ~r1_tarski(B_63, A_64) | ~r1_ordinal1(A_64, B_63) | ~v3_ordinal1(B_63) | ~v3_ordinal1(A_64))), inference(resolution, [status(thm)], [c_102, c_2])).
% 3.01/1.43  tff(c_211, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_ordinal1(B_4, A_3) | ~r1_ordinal1(A_3, B_4) | ~v3_ordinal1(B_4) | ~v3_ordinal1(A_3))), inference(resolution, [status(thm)], [c_10, c_194])).
% 3.01/1.43  tff(c_473, plain, ('#skF_3'='#skF_4' | ~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_471, c_211])).
% 3.01/1.43  tff(c_476, plain, ('#skF_3'='#skF_4' | ~r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_473])).
% 3.01/1.43  tff(c_477, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_476])).
% 3.01/1.43  tff(c_454, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_448])).
% 3.01/1.43  tff(c_460, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_454])).
% 3.01/1.43  tff(c_490, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_460])).
% 3.01/1.43  tff(c_493, plain, (r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_490])).
% 3.01/1.43  tff(c_496, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_493])).
% 3.01/1.43  tff(c_498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_477, c_496])).
% 3.01/1.43  tff(c_499, plain, (~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitRight, [status(thm)], [c_460])).
% 3.01/1.43  tff(c_503, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_499])).
% 3.01/1.43  tff(c_507, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_503])).
% 3.01/1.43  tff(c_508, plain, (~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitRight, [status(thm)], [c_457])).
% 3.01/1.43  tff(c_512, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_508])).
% 3.01/1.43  tff(c_516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_512])).
% 3.01/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.43  
% 3.01/1.43  Inference rules
% 3.01/1.43  ----------------------
% 3.01/1.43  #Ref     : 0
% 3.01/1.43  #Sup     : 90
% 3.01/1.43  #Fact    : 2
% 3.01/1.43  #Define  : 0
% 3.01/1.43  #Split   : 2
% 3.01/1.43  #Chain   : 0
% 3.01/1.43  #Close   : 0
% 3.01/1.43  
% 3.01/1.43  Ordering : KBO
% 3.01/1.43  
% 3.01/1.43  Simplification rules
% 3.01/1.43  ----------------------
% 3.01/1.43  #Subsume      : 13
% 3.01/1.43  #Demod        : 104
% 3.01/1.43  #Tautology    : 35
% 3.01/1.43  #SimpNegUnit  : 2
% 3.01/1.43  #BackRed      : 0
% 3.01/1.43  
% 3.01/1.43  #Partial instantiations: 0
% 3.01/1.43  #Strategies tried      : 1
% 3.01/1.43  
% 3.01/1.43  Timing (in seconds)
% 3.01/1.43  ----------------------
% 3.01/1.43  Preprocessing        : 0.31
% 3.01/1.43  Parsing              : 0.16
% 3.01/1.43  CNF conversion       : 0.02
% 3.01/1.43  Main loop            : 0.35
% 3.01/1.43  Inferencing          : 0.13
% 3.01/1.44  Reduction            : 0.10
% 3.01/1.44  Demodulation         : 0.07
% 3.01/1.44  BG Simplification    : 0.02
% 3.01/1.44  Subsumption          : 0.07
% 3.01/1.44  Abstraction          : 0.02
% 3.01/1.44  MUC search           : 0.00
% 3.01/1.44  Cooper               : 0.00
% 3.01/1.44  Total                : 0.70
% 3.01/1.44  Index Insertion      : 0.00
% 3.01/1.44  Index Deletion       : 0.00
% 3.01/1.44  Index Matching       : 0.00
% 3.01/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
