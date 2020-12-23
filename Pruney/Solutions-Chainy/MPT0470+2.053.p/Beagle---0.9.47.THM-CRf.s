%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:08 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 134 expanded)
%              Number of leaves         :   34 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  149 ( 234 expanded)
%              Number of equality atoms :   34 (  53 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_3 > #skF_5 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_54,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_82,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_127,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_124,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_76,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_115,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_1457,plain,(
    ! [A_182,B_183] :
      ( r2_hidden('#skF_2'(A_182,B_183),B_183)
      | r1_xboole_0(A_182,B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1467,plain,(
    ! [B_184,A_185] :
      ( ~ v1_xboole_0(B_184)
      | r1_xboole_0(A_185,B_184) ) ),
    inference(resolution,[status(thm)],[c_1457,c_2])).

tff(c_42,plain,
    ( k5_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_66,plain,(
    k5_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_44,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [A_34] :
      ( v1_relat_1(A_34)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_64,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( v1_relat_1(k5_relat_1(A_22,B_23))
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_514,plain,(
    ! [A_94,B_95] :
      ( k1_relat_1(k5_relat_1(A_94,B_95)) = k1_relat_1(A_94)
      | ~ r1_tarski(k2_relat_1(A_94),k1_relat_1(B_95))
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_523,plain,(
    ! [B_95] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_95)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_95))
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_514])).

tff(c_530,plain,(
    ! [B_96] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_96)) = k1_xboole_0
      | ~ v1_relat_1(B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_24,c_40,c_523])).

tff(c_30,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(k1_relat_1(A_24))
      | ~ v1_relat_1(A_24)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_539,plain,(
    ! [B_96] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_96))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_96))
      | ~ v1_relat_1(B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_30])).

tff(c_547,plain,(
    ! [B_97] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_97))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_97))
      | ~ v1_relat_1(B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_539])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_562,plain,(
    ! [B_98] :
      ( k5_relat_1(k1_xboole_0,B_98) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_98))
      | ~ v1_relat_1(B_98) ) ),
    inference(resolution,[status(thm)],[c_547,c_8])).

tff(c_566,plain,(
    ! [B_23] :
      ( k5_relat_1(k1_xboole_0,B_23) = k1_xboole_0
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_562])).

tff(c_570,plain,(
    ! [B_99] :
      ( k5_relat_1(k1_xboole_0,B_99) = k1_xboole_0
      | ~ v1_relat_1(B_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_566])).

tff(c_582,plain,(
    k5_relat_1(k1_xboole_0,'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_570])).

tff(c_589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_582])).

tff(c_590,plain,(
    k5_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_678,plain,(
    ! [A_117,B_118] :
      ( r2_hidden('#skF_2'(A_117,B_118),B_118)
      | r1_xboole_0(A_117,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_612,plain,(
    ! [A_103,B_104] :
      ( k3_xboole_0(A_103,B_104) = A_103
      | ~ r1_tarski(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_616,plain,(
    ! [A_20] : k3_xboole_0(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_612])).

tff(c_636,plain,(
    ! [A_109,B_110,C_111] :
      ( ~ r1_xboole_0(A_109,B_110)
      | ~ r2_hidden(C_111,k3_xboole_0(A_109,B_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_639,plain,(
    ! [A_20,C_111] :
      ( ~ r1_xboole_0(k1_xboole_0,A_20)
      | ~ r2_hidden(C_111,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_636])).

tff(c_650,plain,(
    ! [C_111] : ~ r2_hidden(C_111,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_639])).

tff(c_693,plain,(
    ! [A_119] : r1_xboole_0(A_119,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_678,c_650])).

tff(c_20,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_4'(A_16),A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_648,plain,(
    ! [A_109,B_110] :
      ( ~ r1_xboole_0(A_109,B_110)
      | k3_xboole_0(A_109,B_110) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_636])).

tff(c_697,plain,(
    ! [A_119] : k3_xboole_0(A_119,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_693,c_648])).

tff(c_1006,plain,(
    ! [A_153,B_154] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_153,B_154)),k2_relat_1(B_154))
      | ~ v1_relat_1(B_154)
      | ~ v1_relat_1(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1015,plain,(
    ! [A_153] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_153,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1006])).

tff(c_1054,plain,(
    ! [A_158] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_158,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1015])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1057,plain,(
    ! [A_158] :
      ( k3_xboole_0(k2_relat_1(k5_relat_1(A_158,k1_xboole_0)),k1_xboole_0) = k2_relat_1(k5_relat_1(A_158,k1_xboole_0))
      | ~ v1_relat_1(A_158) ) ),
    inference(resolution,[status(thm)],[c_1054,c_22])).

tff(c_1060,plain,(
    ! [A_159] :
      ( k2_relat_1(k5_relat_1(A_159,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_1057])).

tff(c_32,plain,(
    ! [A_25] :
      ( ~ v1_xboole_0(k2_relat_1(A_25))
      | ~ v1_relat_1(A_25)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1078,plain,(
    ! [A_159] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_159,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_159,k1_xboole_0))
      | ~ v1_relat_1(A_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1060,c_32])).

tff(c_1361,plain,(
    ! [A_170] :
      ( ~ v1_relat_1(k5_relat_1(A_170,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_170,k1_xboole_0))
      | ~ v1_relat_1(A_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1078])).

tff(c_1381,plain,(
    ! [A_171] :
      ( k5_relat_1(A_171,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_171,k1_xboole_0))
      | ~ v1_relat_1(A_171) ) ),
    inference(resolution,[status(thm)],[c_1361,c_8])).

tff(c_1388,plain,(
    ! [A_22] :
      ( k5_relat_1(A_22,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_22) ) ),
    inference(resolution,[status(thm)],[c_28,c_1381])).

tff(c_1415,plain,(
    ! [A_174] :
      ( k5_relat_1(A_174,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1388])).

tff(c_1427,plain,(
    k5_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_1415])).

tff(c_1435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_590,c_1427])).

tff(c_1436,plain,(
    ! [A_20] : ~ r1_xboole_0(k1_xboole_0,A_20) ),
    inference(splitRight,[status(thm)],[c_639])).

tff(c_1475,plain,(
    ! [B_184] : ~ v1_xboole_0(B_184) ),
    inference(resolution,[status(thm)],[c_1467,c_1436])).

tff(c_1481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1475,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:53:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.47  
% 3.07/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.47  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_3 > #skF_5 > #skF_2
% 3.07/1.47  
% 3.07/1.47  %Foreground sorts:
% 3.07/1.47  
% 3.07/1.47  
% 3.07/1.47  %Background operators:
% 3.07/1.47  
% 3.07/1.47  
% 3.07/1.47  %Foreground operators:
% 3.07/1.47  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.07/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.07/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.07/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.07/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.07/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.07/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.07/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.07/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.07/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.07/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.07/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.07/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.07/1.47  
% 3.20/1.49  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.20/1.49  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.20/1.49  tff(f_134, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.20/1.49  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.20/1.49  tff(f_86, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.20/1.49  tff(f_92, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.20/1.49  tff(f_82, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.20/1.49  tff(f_127, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.20/1.49  tff(f_124, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 3.20/1.49  tff(f_100, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 3.20/1.49  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.20/1.49  tff(f_80, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.20/1.49  tff(f_68, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.20/1.49  tff(f_76, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.20/1.49  tff(f_115, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.20/1.49  tff(f_108, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.20/1.49  tff(c_1457, plain, (![A_182, B_183]: (r2_hidden('#skF_2'(A_182, B_183), B_183) | r1_xboole_0(A_182, B_183))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.20/1.49  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.49  tff(c_1467, plain, (![B_184, A_185]: (~v1_xboole_0(B_184) | r1_xboole_0(A_185, B_184))), inference(resolution, [status(thm)], [c_1457, c_2])).
% 3.20/1.49  tff(c_42, plain, (k5_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.20/1.49  tff(c_66, plain, (k5_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 3.20/1.49  tff(c_44, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.20/1.49  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.20/1.49  tff(c_60, plain, (![A_34]: (v1_relat_1(A_34) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.20/1.49  tff(c_64, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_60])).
% 3.20/1.49  tff(c_28, plain, (![A_22, B_23]: (v1_relat_1(k5_relat_1(A_22, B_23)) | ~v1_relat_1(B_23) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.20/1.49  tff(c_24, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.20/1.49  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.20/1.49  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.20/1.49  tff(c_514, plain, (![A_94, B_95]: (k1_relat_1(k5_relat_1(A_94, B_95))=k1_relat_1(A_94) | ~r1_tarski(k2_relat_1(A_94), k1_relat_1(B_95)) | ~v1_relat_1(B_95) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.20/1.49  tff(c_523, plain, (![B_95]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_95))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_95)) | ~v1_relat_1(B_95) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_514])).
% 3.20/1.49  tff(c_530, plain, (![B_96]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_96))=k1_xboole_0 | ~v1_relat_1(B_96))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_24, c_40, c_523])).
% 3.20/1.49  tff(c_30, plain, (![A_24]: (~v1_xboole_0(k1_relat_1(A_24)) | ~v1_relat_1(A_24) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.20/1.49  tff(c_539, plain, (![B_96]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_96)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_96)) | ~v1_relat_1(B_96))), inference(superposition, [status(thm), theory('equality')], [c_530, c_30])).
% 3.20/1.49  tff(c_547, plain, (![B_97]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_97)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_97)) | ~v1_relat_1(B_97))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_539])).
% 3.20/1.49  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.20/1.49  tff(c_562, plain, (![B_98]: (k5_relat_1(k1_xboole_0, B_98)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_98)) | ~v1_relat_1(B_98))), inference(resolution, [status(thm)], [c_547, c_8])).
% 3.20/1.49  tff(c_566, plain, (![B_23]: (k5_relat_1(k1_xboole_0, B_23)=k1_xboole_0 | ~v1_relat_1(B_23) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_562])).
% 3.20/1.49  tff(c_570, plain, (![B_99]: (k5_relat_1(k1_xboole_0, B_99)=k1_xboole_0 | ~v1_relat_1(B_99))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_566])).
% 3.20/1.49  tff(c_582, plain, (k5_relat_1(k1_xboole_0, '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_570])).
% 3.20/1.49  tff(c_589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_582])).
% 3.20/1.49  tff(c_590, plain, (k5_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 3.20/1.49  tff(c_678, plain, (![A_117, B_118]: (r2_hidden('#skF_2'(A_117, B_118), B_118) | r1_xboole_0(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.20/1.49  tff(c_612, plain, (![A_103, B_104]: (k3_xboole_0(A_103, B_104)=A_103 | ~r1_tarski(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.20/1.49  tff(c_616, plain, (![A_20]: (k3_xboole_0(k1_xboole_0, A_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_612])).
% 3.20/1.49  tff(c_636, plain, (![A_109, B_110, C_111]: (~r1_xboole_0(A_109, B_110) | ~r2_hidden(C_111, k3_xboole_0(A_109, B_110)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.20/1.49  tff(c_639, plain, (![A_20, C_111]: (~r1_xboole_0(k1_xboole_0, A_20) | ~r2_hidden(C_111, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_616, c_636])).
% 3.20/1.49  tff(c_650, plain, (![C_111]: (~r2_hidden(C_111, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_639])).
% 3.20/1.49  tff(c_693, plain, (![A_119]: (r1_xboole_0(A_119, k1_xboole_0))), inference(resolution, [status(thm)], [c_678, c_650])).
% 3.20/1.49  tff(c_20, plain, (![A_16]: (r2_hidden('#skF_4'(A_16), A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.20/1.49  tff(c_648, plain, (![A_109, B_110]: (~r1_xboole_0(A_109, B_110) | k3_xboole_0(A_109, B_110)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_636])).
% 3.20/1.49  tff(c_697, plain, (![A_119]: (k3_xboole_0(A_119, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_693, c_648])).
% 3.20/1.49  tff(c_1006, plain, (![A_153, B_154]: (r1_tarski(k2_relat_1(k5_relat_1(A_153, B_154)), k2_relat_1(B_154)) | ~v1_relat_1(B_154) | ~v1_relat_1(A_153))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.20/1.49  tff(c_1015, plain, (![A_153]: (r1_tarski(k2_relat_1(k5_relat_1(A_153, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_153))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1006])).
% 3.20/1.49  tff(c_1054, plain, (![A_158]: (r1_tarski(k2_relat_1(k5_relat_1(A_158, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_158))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1015])).
% 3.20/1.49  tff(c_22, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.20/1.49  tff(c_1057, plain, (![A_158]: (k3_xboole_0(k2_relat_1(k5_relat_1(A_158, k1_xboole_0)), k1_xboole_0)=k2_relat_1(k5_relat_1(A_158, k1_xboole_0)) | ~v1_relat_1(A_158))), inference(resolution, [status(thm)], [c_1054, c_22])).
% 3.20/1.49  tff(c_1060, plain, (![A_159]: (k2_relat_1(k5_relat_1(A_159, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_159))), inference(demodulation, [status(thm), theory('equality')], [c_697, c_1057])).
% 3.20/1.49  tff(c_32, plain, (![A_25]: (~v1_xboole_0(k2_relat_1(A_25)) | ~v1_relat_1(A_25) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.20/1.49  tff(c_1078, plain, (![A_159]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_159, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_159, k1_xboole_0)) | ~v1_relat_1(A_159))), inference(superposition, [status(thm), theory('equality')], [c_1060, c_32])).
% 3.20/1.49  tff(c_1361, plain, (![A_170]: (~v1_relat_1(k5_relat_1(A_170, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_170, k1_xboole_0)) | ~v1_relat_1(A_170))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1078])).
% 3.20/1.49  tff(c_1381, plain, (![A_171]: (k5_relat_1(A_171, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_171, k1_xboole_0)) | ~v1_relat_1(A_171))), inference(resolution, [status(thm)], [c_1361, c_8])).
% 3.20/1.49  tff(c_1388, plain, (![A_22]: (k5_relat_1(A_22, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_22))), inference(resolution, [status(thm)], [c_28, c_1381])).
% 3.20/1.49  tff(c_1415, plain, (![A_174]: (k5_relat_1(A_174, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_174))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1388])).
% 3.20/1.49  tff(c_1427, plain, (k5_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_1415])).
% 3.20/1.49  tff(c_1435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_590, c_1427])).
% 3.20/1.49  tff(c_1436, plain, (![A_20]: (~r1_xboole_0(k1_xboole_0, A_20))), inference(splitRight, [status(thm)], [c_639])).
% 3.20/1.49  tff(c_1475, plain, (![B_184]: (~v1_xboole_0(B_184))), inference(resolution, [status(thm)], [c_1467, c_1436])).
% 3.20/1.49  tff(c_1481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1475, c_6])).
% 3.20/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.49  
% 3.20/1.49  Inference rules
% 3.20/1.49  ----------------------
% 3.20/1.49  #Ref     : 0
% 3.20/1.49  #Sup     : 317
% 3.20/1.49  #Fact    : 0
% 3.20/1.49  #Define  : 0
% 3.20/1.49  #Split   : 3
% 3.20/1.49  #Chain   : 0
% 3.20/1.49  #Close   : 0
% 3.20/1.49  
% 3.20/1.49  Ordering : KBO
% 3.20/1.49  
% 3.20/1.49  Simplification rules
% 3.20/1.49  ----------------------
% 3.20/1.49  #Subsume      : 50
% 3.20/1.49  #Demod        : 256
% 3.20/1.49  #Tautology    : 178
% 3.20/1.49  #SimpNegUnit  : 15
% 3.20/1.49  #BackRed      : 3
% 3.20/1.49  
% 3.20/1.49  #Partial instantiations: 0
% 3.20/1.49  #Strategies tried      : 1
% 3.20/1.49  
% 3.20/1.49  Timing (in seconds)
% 3.20/1.49  ----------------------
% 3.20/1.49  Preprocessing        : 0.31
% 3.20/1.49  Parsing              : 0.18
% 3.20/1.49  CNF conversion       : 0.02
% 3.20/1.49  Main loop            : 0.41
% 3.20/1.49  Inferencing          : 0.17
% 3.20/1.49  Reduction            : 0.11
% 3.20/1.49  Demodulation         : 0.08
% 3.20/1.49  BG Simplification    : 0.02
% 3.20/1.49  Subsumption          : 0.07
% 3.20/1.49  Abstraction          : 0.02
% 3.20/1.49  MUC search           : 0.00
% 3.20/1.49  Cooper               : 0.00
% 3.20/1.49  Total                : 0.75
% 3.20/1.49  Index Insertion      : 0.00
% 3.20/1.49  Index Deletion       : 0.00
% 3.20/1.49  Index Matching       : 0.00
% 3.20/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
