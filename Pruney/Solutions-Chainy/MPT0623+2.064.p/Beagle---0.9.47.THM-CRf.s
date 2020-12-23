%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:14 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 180 expanded)
%              Number of leaves         :   36 (  75 expanded)
%              Depth                    :    9
%              Number of atoms          :  144 ( 418 expanded)
%              Number of equality atoms :   72 ( 212 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > np__1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(np__1,type,(
    np__1: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_80,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_47,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_62,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_93,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_42,plain,(
    ! [A_32] : v1_relat_1('#skF_6'(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40,plain,(
    ! [A_32] : v1_funct_1('#skF_6'(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    ! [A_32] : k1_relat_1('#skF_6'(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_67,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_444,plain,(
    ! [A_137,B_138] :
      ( r2_hidden(k4_tarski('#skF_2'(A_137,B_138),'#skF_3'(A_137,B_138)),A_137)
      | r2_hidden('#skF_4'(A_137,B_138),B_138)
      | k1_relat_1(A_137) = B_138 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_87,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,B_59) = A_58
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_95,plain,(
    ! [A_8] : k3_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_87])).

tff(c_180,plain,(
    ! [A_73,B_74,C_75] :
      ( ~ r1_xboole_0(A_73,B_74)
      | ~ r2_hidden(C_75,k3_xboole_0(A_73,B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_183,plain,(
    ! [A_8,C_75] :
      ( ~ r1_xboole_0(k1_xboole_0,A_8)
      | ~ r2_hidden(C_75,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_180])).

tff(c_189,plain,(
    ! [C_75] : ~ r2_hidden(C_75,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_503,plain,(
    ! [B_138] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_138),B_138)
      | k1_relat_1(k1_xboole_0) = B_138 ) ),
    inference(resolution,[status(thm)],[c_444,c_189])).

tff(c_525,plain,(
    ! [B_139] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_139),B_139)
      | k1_xboole_0 = B_139 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_503])).

tff(c_46,plain,(
    ! [A_38,B_42] :
      ( k1_relat_1('#skF_7'(A_38,B_42)) = A_38
      | k1_xboole_0 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_48,plain,(
    ! [A_38,B_42] :
      ( v1_funct_1('#skF_7'(A_38,B_42))
      | k1_xboole_0 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_50,plain,(
    ! [A_38,B_42] :
      ( v1_relat_1('#skF_7'(A_38,B_42))
      | k1_xboole_0 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k1_tarski(A_10),B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_119,plain,(
    ! [A_65,B_66] :
      ( k2_relat_1('#skF_7'(A_65,B_66)) = k1_tarski(B_66)
      | k1_xboole_0 = A_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_52,plain,(
    ! [C_45] :
      ( ~ r1_tarski(k2_relat_1(C_45),'#skF_8')
      | k1_relat_1(C_45) != '#skF_9'
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_190,plain,(
    ! [B_77,A_78] :
      ( ~ r1_tarski(k1_tarski(B_77),'#skF_8')
      | k1_relat_1('#skF_7'(A_78,B_77)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_78,B_77))
      | ~ v1_relat_1('#skF_7'(A_78,B_77))
      | k1_xboole_0 = A_78 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_52])).

tff(c_283,plain,(
    ! [A_99,A_100] :
      ( k1_relat_1('#skF_7'(A_99,A_100)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_99,A_100))
      | ~ v1_relat_1('#skF_7'(A_99,A_100))
      | k1_xboole_0 = A_99
      | ~ r2_hidden(A_100,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_14,c_190])).

tff(c_359,plain,(
    ! [A_116,B_117] :
      ( k1_relat_1('#skF_7'(A_116,B_117)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_116,B_117))
      | ~ r2_hidden(B_117,'#skF_8')
      | k1_xboole_0 = A_116 ) ),
    inference(resolution,[status(thm)],[c_50,c_283])).

tff(c_364,plain,(
    ! [A_118,B_119] :
      ( k1_relat_1('#skF_7'(A_118,B_119)) != '#skF_9'
      | ~ r2_hidden(B_119,'#skF_8')
      | k1_xboole_0 = A_118 ) ),
    inference(resolution,[status(thm)],[c_48,c_359])).

tff(c_367,plain,(
    ! [A_38,B_42] :
      ( A_38 != '#skF_9'
      | ~ r2_hidden(B_42,'#skF_8')
      | k1_xboole_0 = A_38
      | k1_xboole_0 = A_38 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_364])).

tff(c_368,plain,(
    ! [B_42] : ~ r2_hidden(B_42,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_367])).

tff(c_565,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_525,c_368])).

tff(c_598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_565])).

tff(c_600,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_151,plain,(
    ! [A_71] :
      ( k2_relat_1(A_71) = k1_xboole_0
      | k1_relat_1(A_71) != k1_xboole_0
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_157,plain,(
    ! [A_32] :
      ( k2_relat_1('#skF_6'(A_32)) = k1_xboole_0
      | k1_relat_1('#skF_6'(A_32)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_151])).

tff(c_162,plain,(
    ! [A_72] :
      ( k2_relat_1('#skF_6'(A_72)) = k1_xboole_0
      | k1_xboole_0 != A_72 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_157])).

tff(c_171,plain,(
    ! [A_72] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_8')
      | k1_relat_1('#skF_6'(A_72)) != '#skF_9'
      | ~ v1_funct_1('#skF_6'(A_72))
      | ~ v1_relat_1('#skF_6'(A_72))
      | k1_xboole_0 != A_72 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_52])).

tff(c_178,plain,(
    ! [A_72] :
      ( A_72 != '#skF_9'
      | k1_xboole_0 != A_72 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_8,c_171])).

tff(c_187,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_178])).

tff(c_626,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_187])).

tff(c_628,plain,(
    ! [A_140] : ~ r1_xboole_0(k1_xboole_0,A_140) ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_633,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_628])).

tff(c_635,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_634,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_650,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_634])).

tff(c_643,plain,(
    ! [A_8] : r1_tarski('#skF_9',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_8])).

tff(c_660,plain,(
    ! [A_8] : r1_tarski('#skF_8',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_643])).

tff(c_34,plain,(
    ! [A_31] :
      ( k2_relat_1(A_31) = k1_xboole_0
      | k1_relat_1(A_31) != k1_xboole_0
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_730,plain,(
    ! [A_159] :
      ( k2_relat_1(A_159) = '#skF_8'
      | k1_relat_1(A_159) != '#skF_8'
      | ~ v1_relat_1(A_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_635,c_34])).

tff(c_736,plain,(
    ! [A_32] :
      ( k2_relat_1('#skF_6'(A_32)) = '#skF_8'
      | k1_relat_1('#skF_6'(A_32)) != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_42,c_730])).

tff(c_741,plain,(
    ! [A_160] :
      ( k2_relat_1('#skF_6'(A_160)) = '#skF_8'
      | A_160 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_736])).

tff(c_655,plain,(
    ! [C_45] :
      ( ~ r1_tarski(k2_relat_1(C_45),'#skF_8')
      | k1_relat_1(C_45) != '#skF_8'
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_52])).

tff(c_747,plain,(
    ! [A_160] :
      ( ~ r1_tarski('#skF_8','#skF_8')
      | k1_relat_1('#skF_6'(A_160)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_160))
      | ~ v1_relat_1('#skF_6'(A_160))
      | A_160 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_741,c_655])).

tff(c_753,plain,(
    ! [A_160] : A_160 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_660,c_747])).

tff(c_713,plain,(
    ! [A_156,B_157] :
      ( k3_xboole_0(A_156,B_157) = A_156
      | ~ r1_tarski(A_156,B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_721,plain,(
    ! [A_8] : k3_xboole_0('#skF_8',A_8) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_660,c_713])).

tff(c_765,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_753,c_721])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.48  
% 2.82/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.48  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > np__1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_6 > #skF_4
% 2.82/1.48  
% 2.82/1.48  %Foreground sorts:
% 2.82/1.48  
% 2.82/1.48  
% 2.82/1.48  %Background operators:
% 2.82/1.48  
% 2.82/1.48  
% 2.82/1.48  %Foreground operators:
% 2.82/1.48  tff(np__1, type, np__1: $i).
% 2.82/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.82/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.82/1.48  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.82/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.82/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.82/1.48  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.82/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.82/1.48  tff('#skF_9', type, '#skF_9': $i).
% 2.82/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.82/1.48  tff('#skF_8', type, '#skF_8': $i).
% 2.82/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.82/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.82/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.82/1.48  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.82/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.82/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.82/1.48  tff('#skF_6', type, '#skF_6': $i > $i).
% 2.82/1.48  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.82/1.48  
% 2.82/1.50  tff(f_80, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 2.82/1.50  tff(f_47, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.82/1.50  tff(f_111, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 2.82/1.50  tff(f_62, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.82/1.50  tff(f_59, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.82/1.50  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.82/1.50  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.82/1.50  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.82/1.50  tff(f_93, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 2.82/1.50  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.82/1.50  tff(f_68, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.82/1.50  tff(c_42, plain, (![A_32]: (v1_relat_1('#skF_6'(A_32)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.82/1.50  tff(c_40, plain, (![A_32]: (v1_funct_1('#skF_6'(A_32)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.82/1.50  tff(c_38, plain, (![A_32]: (k1_relat_1('#skF_6'(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.82/1.50  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.82/1.50  tff(c_54, plain, (k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.82/1.50  tff(c_67, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_54])).
% 2.82/1.50  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.82/1.50  tff(c_444, plain, (![A_137, B_138]: (r2_hidden(k4_tarski('#skF_2'(A_137, B_138), '#skF_3'(A_137, B_138)), A_137) | r2_hidden('#skF_4'(A_137, B_138), B_138) | k1_relat_1(A_137)=B_138)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.82/1.50  tff(c_8, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.82/1.50  tff(c_87, plain, (![A_58, B_59]: (k3_xboole_0(A_58, B_59)=A_58 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.82/1.50  tff(c_95, plain, (![A_8]: (k3_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_87])).
% 2.82/1.50  tff(c_180, plain, (![A_73, B_74, C_75]: (~r1_xboole_0(A_73, B_74) | ~r2_hidden(C_75, k3_xboole_0(A_73, B_74)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.82/1.50  tff(c_183, plain, (![A_8, C_75]: (~r1_xboole_0(k1_xboole_0, A_8) | ~r2_hidden(C_75, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_95, c_180])).
% 2.82/1.50  tff(c_189, plain, (![C_75]: (~r2_hidden(C_75, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_183])).
% 2.82/1.50  tff(c_503, plain, (![B_138]: (r2_hidden('#skF_4'(k1_xboole_0, B_138), B_138) | k1_relat_1(k1_xboole_0)=B_138)), inference(resolution, [status(thm)], [c_444, c_189])).
% 2.82/1.50  tff(c_525, plain, (![B_139]: (r2_hidden('#skF_4'(k1_xboole_0, B_139), B_139) | k1_xboole_0=B_139)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_503])).
% 2.82/1.50  tff(c_46, plain, (![A_38, B_42]: (k1_relat_1('#skF_7'(A_38, B_42))=A_38 | k1_xboole_0=A_38)), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.82/1.50  tff(c_48, plain, (![A_38, B_42]: (v1_funct_1('#skF_7'(A_38, B_42)) | k1_xboole_0=A_38)), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.82/1.50  tff(c_50, plain, (![A_38, B_42]: (v1_relat_1('#skF_7'(A_38, B_42)) | k1_xboole_0=A_38)), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.82/1.50  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k1_tarski(A_10), B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.82/1.50  tff(c_119, plain, (![A_65, B_66]: (k2_relat_1('#skF_7'(A_65, B_66))=k1_tarski(B_66) | k1_xboole_0=A_65)), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.82/1.50  tff(c_52, plain, (![C_45]: (~r1_tarski(k2_relat_1(C_45), '#skF_8') | k1_relat_1(C_45)!='#skF_9' | ~v1_funct_1(C_45) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.82/1.50  tff(c_190, plain, (![B_77, A_78]: (~r1_tarski(k1_tarski(B_77), '#skF_8') | k1_relat_1('#skF_7'(A_78, B_77))!='#skF_9' | ~v1_funct_1('#skF_7'(A_78, B_77)) | ~v1_relat_1('#skF_7'(A_78, B_77)) | k1_xboole_0=A_78)), inference(superposition, [status(thm), theory('equality')], [c_119, c_52])).
% 2.82/1.50  tff(c_283, plain, (![A_99, A_100]: (k1_relat_1('#skF_7'(A_99, A_100))!='#skF_9' | ~v1_funct_1('#skF_7'(A_99, A_100)) | ~v1_relat_1('#skF_7'(A_99, A_100)) | k1_xboole_0=A_99 | ~r2_hidden(A_100, '#skF_8'))), inference(resolution, [status(thm)], [c_14, c_190])).
% 2.82/1.50  tff(c_359, plain, (![A_116, B_117]: (k1_relat_1('#skF_7'(A_116, B_117))!='#skF_9' | ~v1_funct_1('#skF_7'(A_116, B_117)) | ~r2_hidden(B_117, '#skF_8') | k1_xboole_0=A_116)), inference(resolution, [status(thm)], [c_50, c_283])).
% 2.82/1.50  tff(c_364, plain, (![A_118, B_119]: (k1_relat_1('#skF_7'(A_118, B_119))!='#skF_9' | ~r2_hidden(B_119, '#skF_8') | k1_xboole_0=A_118)), inference(resolution, [status(thm)], [c_48, c_359])).
% 2.82/1.50  tff(c_367, plain, (![A_38, B_42]: (A_38!='#skF_9' | ~r2_hidden(B_42, '#skF_8') | k1_xboole_0=A_38 | k1_xboole_0=A_38)), inference(superposition, [status(thm), theory('equality')], [c_46, c_364])).
% 2.82/1.50  tff(c_368, plain, (![B_42]: (~r2_hidden(B_42, '#skF_8'))), inference(splitLeft, [status(thm)], [c_367])).
% 2.82/1.50  tff(c_565, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_525, c_368])).
% 2.82/1.50  tff(c_598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_565])).
% 2.82/1.50  tff(c_600, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_367])).
% 2.82/1.50  tff(c_151, plain, (![A_71]: (k2_relat_1(A_71)=k1_xboole_0 | k1_relat_1(A_71)!=k1_xboole_0 | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.82/1.50  tff(c_157, plain, (![A_32]: (k2_relat_1('#skF_6'(A_32))=k1_xboole_0 | k1_relat_1('#skF_6'(A_32))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_151])).
% 2.82/1.50  tff(c_162, plain, (![A_72]: (k2_relat_1('#skF_6'(A_72))=k1_xboole_0 | k1_xboole_0!=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_157])).
% 2.82/1.50  tff(c_171, plain, (![A_72]: (~r1_tarski(k1_xboole_0, '#skF_8') | k1_relat_1('#skF_6'(A_72))!='#skF_9' | ~v1_funct_1('#skF_6'(A_72)) | ~v1_relat_1('#skF_6'(A_72)) | k1_xboole_0!=A_72)), inference(superposition, [status(thm), theory('equality')], [c_162, c_52])).
% 2.82/1.50  tff(c_178, plain, (![A_72]: (A_72!='#skF_9' | k1_xboole_0!=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_8, c_171])).
% 2.82/1.50  tff(c_187, plain, (k1_xboole_0!='#skF_9'), inference(reflexivity, [status(thm), theory('equality')], [c_178])).
% 2.82/1.50  tff(c_626, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_600, c_187])).
% 2.82/1.50  tff(c_628, plain, (![A_140]: (~r1_xboole_0(k1_xboole_0, A_140))), inference(splitRight, [status(thm)], [c_183])).
% 2.82/1.50  tff(c_633, plain, $false, inference(resolution, [status(thm)], [c_10, c_628])).
% 2.82/1.50  tff(c_635, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_54])).
% 2.82/1.50  tff(c_634, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_54])).
% 2.82/1.50  tff(c_650, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_635, c_634])).
% 2.82/1.50  tff(c_643, plain, (![A_8]: (r1_tarski('#skF_9', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_634, c_8])).
% 2.82/1.50  tff(c_660, plain, (![A_8]: (r1_tarski('#skF_8', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_650, c_643])).
% 2.82/1.50  tff(c_34, plain, (![A_31]: (k2_relat_1(A_31)=k1_xboole_0 | k1_relat_1(A_31)!=k1_xboole_0 | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.82/1.50  tff(c_730, plain, (![A_159]: (k2_relat_1(A_159)='#skF_8' | k1_relat_1(A_159)!='#skF_8' | ~v1_relat_1(A_159))), inference(demodulation, [status(thm), theory('equality')], [c_635, c_635, c_34])).
% 2.82/1.50  tff(c_736, plain, (![A_32]: (k2_relat_1('#skF_6'(A_32))='#skF_8' | k1_relat_1('#skF_6'(A_32))!='#skF_8')), inference(resolution, [status(thm)], [c_42, c_730])).
% 2.82/1.50  tff(c_741, plain, (![A_160]: (k2_relat_1('#skF_6'(A_160))='#skF_8' | A_160!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_736])).
% 2.82/1.50  tff(c_655, plain, (![C_45]: (~r1_tarski(k2_relat_1(C_45), '#skF_8') | k1_relat_1(C_45)!='#skF_8' | ~v1_funct_1(C_45) | ~v1_relat_1(C_45))), inference(demodulation, [status(thm), theory('equality')], [c_650, c_52])).
% 2.82/1.50  tff(c_747, plain, (![A_160]: (~r1_tarski('#skF_8', '#skF_8') | k1_relat_1('#skF_6'(A_160))!='#skF_8' | ~v1_funct_1('#skF_6'(A_160)) | ~v1_relat_1('#skF_6'(A_160)) | A_160!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_741, c_655])).
% 2.82/1.50  tff(c_753, plain, (![A_160]: (A_160!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_660, c_747])).
% 2.82/1.50  tff(c_713, plain, (![A_156, B_157]: (k3_xboole_0(A_156, B_157)=A_156 | ~r1_tarski(A_156, B_157))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.82/1.50  tff(c_721, plain, (![A_8]: (k3_xboole_0('#skF_8', A_8)='#skF_8')), inference(resolution, [status(thm)], [c_660, c_713])).
% 2.82/1.50  tff(c_765, plain, $false, inference(negUnitSimplification, [status(thm)], [c_753, c_721])).
% 2.82/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.50  
% 2.82/1.50  Inference rules
% 2.82/1.50  ----------------------
% 2.82/1.50  #Ref     : 1
% 2.82/1.50  #Sup     : 138
% 2.82/1.50  #Fact    : 0
% 2.82/1.50  #Define  : 0
% 2.82/1.50  #Split   : 6
% 2.82/1.50  #Chain   : 0
% 2.82/1.50  #Close   : 0
% 2.82/1.50  
% 2.82/1.50  Ordering : KBO
% 2.82/1.50  
% 2.82/1.50  Simplification rules
% 2.82/1.50  ----------------------
% 2.82/1.50  #Subsume      : 19
% 2.82/1.50  #Demod        : 94
% 2.82/1.50  #Tautology    : 47
% 2.82/1.50  #SimpNegUnit  : 15
% 2.82/1.50  #BackRed      : 38
% 2.82/1.50  
% 2.82/1.50  #Partial instantiations: 0
% 2.82/1.50  #Strategies tried      : 1
% 2.82/1.50  
% 2.82/1.50  Timing (in seconds)
% 2.82/1.50  ----------------------
% 2.82/1.50  Preprocessing        : 0.31
% 2.82/1.50  Parsing              : 0.16
% 2.82/1.50  CNF conversion       : 0.03
% 2.82/1.50  Main loop            : 0.41
% 2.82/1.50  Inferencing          : 0.15
% 2.82/1.50  Reduction            : 0.12
% 2.82/1.50  Demodulation         : 0.08
% 2.82/1.50  BG Simplification    : 0.02
% 2.82/1.50  Subsumption          : 0.07
% 2.82/1.50  Abstraction          : 0.02
% 2.82/1.50  MUC search           : 0.00
% 2.82/1.50  Cooper               : 0.00
% 2.82/1.50  Total                : 0.76
% 2.82/1.50  Index Insertion      : 0.00
% 2.82/1.50  Index Deletion       : 0.00
% 2.82/1.50  Index Matching       : 0.00
% 2.82/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
