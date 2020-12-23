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
% DateTime   : Thu Dec  3 10:05:46 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 136 expanded)
%              Number of leaves         :   36 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  104 ( 224 expanded)
%              Number of equality atoms :    8 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_10,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_202,plain,(
    ! [A_103,C_104,B_105] :
      ( ~ r2_hidden(A_103,C_104)
      | ~ r1_xboole_0(k2_tarski(A_103,B_105),C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_207,plain,(
    ! [A_103] : ~ r2_hidden(A_103,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_202])).

tff(c_32,plain,(
    ! [A_37] :
      ( r2_hidden('#skF_1'(A_37),A_37)
      | v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_208,plain,(
    ! [A_106] : ~ r2_hidden(A_106,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_202])).

tff(c_213,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_208])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ! [A_55] :
      ( v1_xboole_0(k1_relat_1(A_55))
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_54,plain,(
    ! [A_71] :
      ( v1_xboole_0(k1_relat_1(A_71))
      | ~ v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_65,plain,(
    ! [A_74] :
      ( k1_relat_1(A_74) = k1_xboole_0
      | ~ v1_xboole_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_70,plain,(
    ! [A_75] :
      ( k1_relat_1(k1_relat_1(A_75)) = k1_xboole_0
      | ~ v1_xboole_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_34,c_65])).

tff(c_36,plain,(
    ! [A_56] :
      ( v1_funct_1(A_56)
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_61,plain,(
    ! [A_71] :
      ( v1_funct_1(k1_relat_1(A_71))
      | ~ v1_xboole_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_54,c_36])).

tff(c_79,plain,(
    ! [A_75] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_75))
      | ~ v1_xboole_0(A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_61])).

tff(c_109,plain,(
    ! [A_83] :
      ( ~ v1_xboole_0(k1_relat_1(A_83))
      | ~ v1_xboole_0(A_83) ) ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_116,plain,(
    ! [A_55] : ~ v1_xboole_0(A_55) ),
    inference(resolution,[status(thm)],[c_34,c_109])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( ~ r1_xboole_0(B_6,A_5)
      | ~ r1_tarski(B_6,A_5)
      | v1_xboole_0(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_133,plain,(
    ! [B_89,A_90] :
      ( ~ r1_xboole_0(B_89,A_90)
      | ~ r1_tarski(B_89,A_90) ) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_12])).

tff(c_138,plain,(
    ! [A_91] : ~ r1_tarski(A_91,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_133])).

tff(c_143,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_8,c_138])).

tff(c_144,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_82,plain,(
    ! [A_75] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_75))
      | ~ v1_xboole_0(A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_34])).

tff(c_153,plain,(
    ! [A_94] :
      ( ~ v1_xboole_0(k1_relat_1(A_94))
      | ~ v1_xboole_0(A_94) ) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_160,plain,(
    ! [A_55] : ~ v1_xboole_0(A_55) ),
    inference(resolution,[status(thm)],[c_34,c_153])).

tff(c_176,plain,(
    ! [B_100,A_101] :
      ( ~ r1_xboole_0(B_100,A_101)
      | ~ r1_tarski(B_100,A_101) ) ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_12])).

tff(c_181,plain,(
    ! [A_102] : ~ r1_tarski(A_102,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_176])).

tff(c_186,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_8,c_181])).

tff(c_187,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_62,plain,(
    ! [A_71] :
      ( k1_relat_1(A_71) = k1_xboole_0
      | ~ v1_xboole_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_197,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_187,c_62])).

tff(c_303,plain,(
    ! [A_135,B_136] :
      ( r2_hidden('#skF_4'(A_135,B_136),k1_relat_1(B_136))
      | v5_funct_1(B_136,A_135)
      | ~ v1_funct_1(B_136)
      | ~ v1_relat_1(B_136)
      | ~ v1_funct_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_306,plain,(
    ! [A_135] :
      ( r2_hidden('#skF_4'(A_135,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_135)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_303])).

tff(c_311,plain,(
    ! [A_135] :
      ( r2_hidden('#skF_4'(A_135,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_135)
      | ~ v1_funct_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_144,c_306])).

tff(c_314,plain,(
    ! [A_137] :
      ( v5_funct_1(k1_xboole_0,A_137)
      | ~ v1_funct_1(A_137)
      | ~ v1_relat_1(A_137) ) ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_311])).

tff(c_44,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_317,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_314,c_44])).

tff(c_321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.27  
% 2.16/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.27  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.16/1.27  
% 2.16/1.27  %Foreground sorts:
% 2.16/1.27  
% 2.16/1.27  
% 2.16/1.27  %Background operators:
% 2.16/1.27  
% 2.16/1.27  
% 2.16/1.27  %Foreground operators:
% 2.16/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.16/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.16/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.16/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.16/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.27  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.16/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.16/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.16/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.16/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.16/1.27  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.16/1.27  
% 2.16/1.28  tff(f_103, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 2.16/1.28  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.16/1.28  tff(f_62, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.16/1.28  tff(f_72, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.16/1.28  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.16/1.28  tff(f_76, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.16/1.28  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.16/1.28  tff(f_80, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.16/1.28  tff(f_45, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.16/1.28  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 2.16/1.28  tff(c_48, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.16/1.28  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.16/1.28  tff(c_10, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.28  tff(c_202, plain, (![A_103, C_104, B_105]: (~r2_hidden(A_103, C_104) | ~r1_xboole_0(k2_tarski(A_103, B_105), C_104))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.16/1.28  tff(c_207, plain, (![A_103]: (~r2_hidden(A_103, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_202])).
% 2.16/1.28  tff(c_32, plain, (![A_37]: (r2_hidden('#skF_1'(A_37), A_37) | v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.16/1.28  tff(c_208, plain, (![A_106]: (~r2_hidden(A_106, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_202])).
% 2.16/1.28  tff(c_213, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_208])).
% 2.16/1.28  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.28  tff(c_34, plain, (![A_55]: (v1_xboole_0(k1_relat_1(A_55)) | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.16/1.28  tff(c_54, plain, (![A_71]: (v1_xboole_0(k1_relat_1(A_71)) | ~v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.16/1.28  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.28  tff(c_65, plain, (![A_74]: (k1_relat_1(A_74)=k1_xboole_0 | ~v1_xboole_0(A_74))), inference(resolution, [status(thm)], [c_54, c_2])).
% 2.16/1.28  tff(c_70, plain, (![A_75]: (k1_relat_1(k1_relat_1(A_75))=k1_xboole_0 | ~v1_xboole_0(A_75))), inference(resolution, [status(thm)], [c_34, c_65])).
% 2.16/1.28  tff(c_36, plain, (![A_56]: (v1_funct_1(A_56) | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.16/1.28  tff(c_61, plain, (![A_71]: (v1_funct_1(k1_relat_1(A_71)) | ~v1_xboole_0(A_71))), inference(resolution, [status(thm)], [c_54, c_36])).
% 2.16/1.28  tff(c_79, plain, (![A_75]: (v1_funct_1(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_75)) | ~v1_xboole_0(A_75))), inference(superposition, [status(thm), theory('equality')], [c_70, c_61])).
% 2.16/1.28  tff(c_109, plain, (![A_83]: (~v1_xboole_0(k1_relat_1(A_83)) | ~v1_xboole_0(A_83))), inference(splitLeft, [status(thm)], [c_79])).
% 2.16/1.28  tff(c_116, plain, (![A_55]: (~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_34, c_109])).
% 2.16/1.28  tff(c_12, plain, (![B_6, A_5]: (~r1_xboole_0(B_6, A_5) | ~r1_tarski(B_6, A_5) | v1_xboole_0(B_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.16/1.28  tff(c_133, plain, (![B_89, A_90]: (~r1_xboole_0(B_89, A_90) | ~r1_tarski(B_89, A_90))), inference(negUnitSimplification, [status(thm)], [c_116, c_12])).
% 2.16/1.28  tff(c_138, plain, (![A_91]: (~r1_tarski(A_91, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_133])).
% 2.16/1.28  tff(c_143, plain, $false, inference(resolution, [status(thm)], [c_8, c_138])).
% 2.16/1.28  tff(c_144, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_79])).
% 2.16/1.28  tff(c_82, plain, (![A_75]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_75)) | ~v1_xboole_0(A_75))), inference(superposition, [status(thm), theory('equality')], [c_70, c_34])).
% 2.16/1.28  tff(c_153, plain, (![A_94]: (~v1_xboole_0(k1_relat_1(A_94)) | ~v1_xboole_0(A_94))), inference(splitLeft, [status(thm)], [c_82])).
% 2.16/1.28  tff(c_160, plain, (![A_55]: (~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_34, c_153])).
% 2.16/1.28  tff(c_176, plain, (![B_100, A_101]: (~r1_xboole_0(B_100, A_101) | ~r1_tarski(B_100, A_101))), inference(negUnitSimplification, [status(thm)], [c_160, c_12])).
% 2.16/1.28  tff(c_181, plain, (![A_102]: (~r1_tarski(A_102, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_176])).
% 2.16/1.28  tff(c_186, plain, $false, inference(resolution, [status(thm)], [c_8, c_181])).
% 2.16/1.28  tff(c_187, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_82])).
% 2.16/1.28  tff(c_62, plain, (![A_71]: (k1_relat_1(A_71)=k1_xboole_0 | ~v1_xboole_0(A_71))), inference(resolution, [status(thm)], [c_54, c_2])).
% 2.16/1.28  tff(c_197, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_187, c_62])).
% 2.16/1.28  tff(c_303, plain, (![A_135, B_136]: (r2_hidden('#skF_4'(A_135, B_136), k1_relat_1(B_136)) | v5_funct_1(B_136, A_135) | ~v1_funct_1(B_136) | ~v1_relat_1(B_136) | ~v1_funct_1(A_135) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.16/1.28  tff(c_306, plain, (![A_135]: (r2_hidden('#skF_4'(A_135, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_135) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_135) | ~v1_relat_1(A_135))), inference(superposition, [status(thm), theory('equality')], [c_197, c_303])).
% 2.16/1.28  tff(c_311, plain, (![A_135]: (r2_hidden('#skF_4'(A_135, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_135) | ~v1_funct_1(A_135) | ~v1_relat_1(A_135))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_144, c_306])).
% 2.16/1.28  tff(c_314, plain, (![A_137]: (v5_funct_1(k1_xboole_0, A_137) | ~v1_funct_1(A_137) | ~v1_relat_1(A_137))), inference(negUnitSimplification, [status(thm)], [c_207, c_311])).
% 2.16/1.28  tff(c_44, plain, (~v5_funct_1(k1_xboole_0, '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.16/1.28  tff(c_317, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_314, c_44])).
% 2.16/1.28  tff(c_321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_317])).
% 2.16/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.28  
% 2.16/1.28  Inference rules
% 2.16/1.28  ----------------------
% 2.16/1.28  #Ref     : 1
% 2.16/1.28  #Sup     : 52
% 2.16/1.28  #Fact    : 0
% 2.16/1.28  #Define  : 0
% 2.16/1.28  #Split   : 2
% 2.16/1.28  #Chain   : 0
% 2.16/1.28  #Close   : 0
% 2.16/1.28  
% 2.16/1.28  Ordering : KBO
% 2.16/1.28  
% 2.16/1.28  Simplification rules
% 2.16/1.28  ----------------------
% 2.16/1.28  #Subsume      : 17
% 2.16/1.28  #Demod        : 17
% 2.16/1.28  #Tautology    : 28
% 2.16/1.28  #SimpNegUnit  : 7
% 2.16/1.28  #BackRed      : 0
% 2.16/1.28  
% 2.16/1.28  #Partial instantiations: 0
% 2.16/1.28  #Strategies tried      : 1
% 2.16/1.28  
% 2.16/1.28  Timing (in seconds)
% 2.16/1.28  ----------------------
% 2.16/1.29  Preprocessing        : 0.33
% 2.16/1.29  Parsing              : 0.17
% 2.16/1.29  CNF conversion       : 0.02
% 2.16/1.29  Main loop            : 0.19
% 2.16/1.29  Inferencing          : 0.07
% 2.16/1.29  Reduction            : 0.05
% 2.16/1.29  Demodulation         : 0.04
% 2.16/1.29  BG Simplification    : 0.02
% 2.16/1.29  Subsumption          : 0.03
% 2.16/1.29  Abstraction          : 0.01
% 2.16/1.29  MUC search           : 0.00
% 2.16/1.29  Cooper               : 0.00
% 2.16/1.29  Total                : 0.55
% 2.16/1.29  Index Insertion      : 0.00
% 2.16/1.29  Index Deletion       : 0.00
% 2.16/1.29  Index Matching       : 0.00
% 2.16/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
