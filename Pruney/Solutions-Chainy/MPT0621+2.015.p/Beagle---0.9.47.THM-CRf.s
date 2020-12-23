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
% DateTime   : Thu Dec  3 10:03:00 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 141 expanded)
%              Number of leaves         :   24 (  60 expanded)
%              Depth                    :   18
%              Number of atoms          :  141 ( 341 expanded)
%              Number of equality atoms :   66 ( 130 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_3 > #skF_5 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_72,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_60,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(c_30,plain,(
    ! [A_20] : v1_relat_1('#skF_4'(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [A_20] : k1_relat_1('#skF_4'(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_107,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_2'(A_54,B_55),A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_115,plain,(
    ! [A_54] : r1_tarski(A_54,A_54) ),
    inference(resolution,[status(thm)],[c_107,c_8])).

tff(c_218,plain,(
    ! [B_73,A_74] :
      ( k7_relat_1(B_73,A_74) = B_73
      | ~ r1_tarski(k1_relat_1(B_73),A_74)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_248,plain,(
    ! [B_77] :
      ( k7_relat_1(B_77,k1_relat_1(B_77)) = B_77
      | ~ v1_relat_1(B_77) ) ),
    inference(resolution,[status(thm)],[c_115,c_218])).

tff(c_260,plain,(
    ! [A_20] :
      ( k7_relat_1('#skF_4'(A_20),A_20) = '#skF_4'(A_20)
      | ~ v1_relat_1('#skF_4'(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_248])).

tff(c_267,plain,(
    ! [A_78] : k7_relat_1('#skF_4'(A_78),A_78) = '#skF_4'(A_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_260])).

tff(c_74,plain,(
    ! [A_46] :
      ( k7_relat_1(A_46,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_82,plain,(
    ! [A_20] : k7_relat_1('#skF_4'(A_20),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_74])).

tff(c_274,plain,(
    '#skF_4'(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_82])).

tff(c_319,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_26])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,(
    ! [C_59,B_60,A_61] :
      ( r2_hidden(C_59,B_60)
      | ~ r2_hidden(C_59,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_125,plain,(
    ! [A_1,B_60] :
      ( r2_hidden('#skF_1'(A_1),B_60)
      | ~ r1_tarski(A_1,B_60)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_119])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    ! [A_20] : v1_funct_1('#skF_4'(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [A_13,B_14] : v1_funct_1('#skF_3'(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [A_13,B_14] : k1_relat_1('#skF_3'(A_13,B_14)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    ! [A_13,B_14] : v1_relat_1('#skF_3'(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_63,plain,(
    ! [C_44,B_45] :
      ( C_44 = B_45
      | k1_relat_1(C_44) != '#skF_5'
      | k1_relat_1(B_45) != '#skF_5'
      | ~ v1_funct_1(C_44)
      | ~ v1_relat_1(C_44)
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_65,plain,(
    ! [B_45,A_13,B_14] :
      ( B_45 = '#skF_3'(A_13,B_14)
      | k1_relat_1('#skF_3'(A_13,B_14)) != '#skF_5'
      | k1_relat_1(B_45) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_13,B_14))
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_22,c_63])).

tff(c_291,plain,(
    ! [B_79,A_80,B_81] :
      ( B_79 = '#skF_3'(A_80,B_81)
      | A_80 != '#skF_5'
      | k1_relat_1(B_79) != '#skF_5'
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_65])).

tff(c_295,plain,(
    ! [A_20,A_80,B_81] :
      ( '#skF_4'(A_20) = '#skF_3'(A_80,B_81)
      | A_80 != '#skF_5'
      | k1_relat_1('#skF_4'(A_20)) != '#skF_5'
      | ~ v1_funct_1('#skF_4'(A_20)) ) ),
    inference(resolution,[status(thm)],[c_30,c_291])).

tff(c_902,plain,(
    ! [A_1052,A_1053,B_1054] :
      ( '#skF_4'(A_1052) = '#skF_3'(A_1053,B_1054)
      | A_1053 != '#skF_5'
      | A_1052 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_295])).

tff(c_257,plain,(
    ! [A_13,B_14] :
      ( k7_relat_1('#skF_3'(A_13,B_14),A_13) = '#skF_3'(A_13,B_14)
      | ~ v1_relat_1('#skF_3'(A_13,B_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_248])).

tff(c_264,plain,(
    ! [A_13,B_14] : k7_relat_1('#skF_3'(A_13,B_14),A_13) = '#skF_3'(A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_257])).

tff(c_1517,plain,(
    ! [A_1661,A_1662,B_1663] :
      ( k7_relat_1('#skF_4'(A_1661),A_1662) = '#skF_3'(A_1662,B_1663)
      | A_1662 != '#skF_5'
      | A_1661 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_902,c_264])).

tff(c_234,plain,(
    ! [B_73] :
      ( k7_relat_1(B_73,k1_relat_1(B_73)) = B_73
      | ~ v1_relat_1(B_73) ) ),
    inference(resolution,[status(thm)],[c_115,c_218])).

tff(c_1559,plain,(
    ! [A_1661,B_1663] :
      ( '#skF_3'(k1_relat_1('#skF_4'(A_1661)),B_1663) = '#skF_4'(A_1661)
      | ~ v1_relat_1('#skF_4'(A_1661))
      | k1_relat_1('#skF_4'(A_1661)) != '#skF_5'
      | A_1661 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1517,c_234])).

tff(c_1635,plain,(
    ! [A_1664,B_1665] :
      ( '#skF_4'(A_1664) = '#skF_3'(A_1664,B_1665)
      | A_1664 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30,c_26,c_1559])).

tff(c_16,plain,(
    ! [A_13,B_14,D_19] :
      ( k1_funct_1('#skF_3'(A_13,B_14),D_19) = B_14
      | ~ r2_hidden(D_19,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2340,plain,(
    ! [A_1685,D_1686] :
      ( k1_funct_1('#skF_4'(A_1685),D_1686) = '#skF_5'
      | ~ r2_hidden(D_1686,A_1685)
      | A_1685 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1635,c_16])).

tff(c_24,plain,(
    ! [A_20,C_25] :
      ( k1_funct_1('#skF_4'(A_20),C_25) = k1_xboole_0
      | ~ r2_hidden(C_25,A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2343,plain,(
    ! [D_1686,A_1685] :
      ( k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(D_1686,A_1685)
      | ~ r2_hidden(D_1686,A_1685)
      | A_1685 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2340,c_24])).

tff(c_2448,plain,(
    ! [D_2403,A_2404] :
      ( ~ r2_hidden(D_2403,A_2404)
      | ~ r2_hidden(D_2403,A_2404)
      | A_2404 != '#skF_5' ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2343])).

tff(c_2462,plain,(
    ! [A_2416] :
      ( ~ r2_hidden('#skF_1'(A_2416),A_2416)
      | A_2416 != '#skF_5'
      | v1_xboole_0(A_2416) ) ),
    inference(resolution,[status(thm)],[c_4,c_2448])).

tff(c_2468,plain,(
    ! [B_60] :
      ( B_60 != '#skF_5'
      | ~ r1_tarski(B_60,B_60)
      | v1_xboole_0(B_60) ) ),
    inference(resolution,[status(thm)],[c_125,c_2462])).

tff(c_2477,plain,(
    ! [B_2428] :
      ( B_2428 != '#skF_5'
      | v1_xboole_0(B_2428) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_2468])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    ! [A_54,B_55] :
      ( ~ v1_xboole_0(A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_107,c_2])).

tff(c_232,plain,(
    ! [A_20,A_74] :
      ( k7_relat_1('#skF_4'(A_20),A_74) = '#skF_4'(A_20)
      | ~ r1_tarski(A_20,A_74)
      | ~ v1_relat_1('#skF_4'(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_218])).

tff(c_362,plain,(
    ! [A_82,A_83] :
      ( k7_relat_1('#skF_4'(A_82),A_83) = '#skF_4'(A_82)
      | ~ r1_tarski(A_82,A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_232])).

tff(c_424,plain,(
    ! [A_84] :
      ( '#skF_4'(A_84) = k1_xboole_0
      | ~ r1_tarski(A_84,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_362])).

tff(c_433,plain,(
    ! [A_54] :
      ( '#skF_4'(A_54) = k1_xboole_0
      | ~ v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_116,c_424])).

tff(c_2490,plain,(
    ! [B_2440] :
      ( '#skF_4'(B_2440) = k1_xboole_0
      | B_2440 != '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_2477,c_433])).

tff(c_2545,plain,(
    ! [B_2440] :
      ( k1_relat_1(k1_xboole_0) = B_2440
      | B_2440 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2490,c_26])).

tff(c_2585,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_2545])).

tff(c_2609,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2585,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:10:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.68  
% 3.82/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.68  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_3 > #skF_5 > #skF_2
% 3.82/1.68  
% 3.82/1.68  %Foreground sorts:
% 3.82/1.68  
% 3.82/1.68  
% 3.82/1.68  %Background operators:
% 3.82/1.68  
% 3.82/1.68  
% 3.82/1.68  %Foreground operators:
% 3.82/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.82/1.68  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.82/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.82/1.68  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.82/1.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.82/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.82/1.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.82/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.82/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.82/1.68  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.82/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.82/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.82/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.82/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.82/1.68  
% 3.82/1.70  tff(f_72, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 3.82/1.70  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.82/1.70  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.82/1.70  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 3.82/1.70  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.82/1.70  tff(f_91, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 3.82/1.70  tff(f_60, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 3.82/1.70  tff(c_30, plain, (![A_20]: (v1_relat_1('#skF_4'(A_20)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.82/1.70  tff(c_26, plain, (![A_20]: (k1_relat_1('#skF_4'(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.82/1.70  tff(c_107, plain, (![A_54, B_55]: (r2_hidden('#skF_2'(A_54, B_55), A_54) | r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.82/1.70  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.82/1.70  tff(c_115, plain, (![A_54]: (r1_tarski(A_54, A_54))), inference(resolution, [status(thm)], [c_107, c_8])).
% 3.82/1.70  tff(c_218, plain, (![B_73, A_74]: (k7_relat_1(B_73, A_74)=B_73 | ~r1_tarski(k1_relat_1(B_73), A_74) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.82/1.70  tff(c_248, plain, (![B_77]: (k7_relat_1(B_77, k1_relat_1(B_77))=B_77 | ~v1_relat_1(B_77))), inference(resolution, [status(thm)], [c_115, c_218])).
% 3.82/1.70  tff(c_260, plain, (![A_20]: (k7_relat_1('#skF_4'(A_20), A_20)='#skF_4'(A_20) | ~v1_relat_1('#skF_4'(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_248])).
% 3.82/1.70  tff(c_267, plain, (![A_78]: (k7_relat_1('#skF_4'(A_78), A_78)='#skF_4'(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_260])).
% 3.82/1.70  tff(c_74, plain, (![A_46]: (k7_relat_1(A_46, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.82/1.70  tff(c_82, plain, (![A_20]: (k7_relat_1('#skF_4'(A_20), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_74])).
% 3.82/1.70  tff(c_274, plain, ('#skF_4'(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_267, c_82])).
% 3.82/1.70  tff(c_319, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_274, c_26])).
% 3.82/1.70  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.82/1.70  tff(c_119, plain, (![C_59, B_60, A_61]: (r2_hidden(C_59, B_60) | ~r2_hidden(C_59, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.82/1.70  tff(c_125, plain, (![A_1, B_60]: (r2_hidden('#skF_1'(A_1), B_60) | ~r1_tarski(A_1, B_60) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_119])).
% 3.82/1.70  tff(c_32, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.82/1.70  tff(c_28, plain, (![A_20]: (v1_funct_1('#skF_4'(A_20)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.82/1.70  tff(c_20, plain, (![A_13, B_14]: (v1_funct_1('#skF_3'(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.82/1.70  tff(c_18, plain, (![A_13, B_14]: (k1_relat_1('#skF_3'(A_13, B_14))=A_13)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.82/1.70  tff(c_22, plain, (![A_13, B_14]: (v1_relat_1('#skF_3'(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.82/1.70  tff(c_63, plain, (![C_44, B_45]: (C_44=B_45 | k1_relat_1(C_44)!='#skF_5' | k1_relat_1(B_45)!='#skF_5' | ~v1_funct_1(C_44) | ~v1_relat_1(C_44) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.82/1.70  tff(c_65, plain, (![B_45, A_13, B_14]: (B_45='#skF_3'(A_13, B_14) | k1_relat_1('#skF_3'(A_13, B_14))!='#skF_5' | k1_relat_1(B_45)!='#skF_5' | ~v1_funct_1('#skF_3'(A_13, B_14)) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_22, c_63])).
% 3.82/1.70  tff(c_291, plain, (![B_79, A_80, B_81]: (B_79='#skF_3'(A_80, B_81) | A_80!='#skF_5' | k1_relat_1(B_79)!='#skF_5' | ~v1_funct_1(B_79) | ~v1_relat_1(B_79))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_65])).
% 3.82/1.70  tff(c_295, plain, (![A_20, A_80, B_81]: ('#skF_4'(A_20)='#skF_3'(A_80, B_81) | A_80!='#skF_5' | k1_relat_1('#skF_4'(A_20))!='#skF_5' | ~v1_funct_1('#skF_4'(A_20)))), inference(resolution, [status(thm)], [c_30, c_291])).
% 3.82/1.70  tff(c_902, plain, (![A_1052, A_1053, B_1054]: ('#skF_4'(A_1052)='#skF_3'(A_1053, B_1054) | A_1053!='#skF_5' | A_1052!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_295])).
% 3.82/1.70  tff(c_257, plain, (![A_13, B_14]: (k7_relat_1('#skF_3'(A_13, B_14), A_13)='#skF_3'(A_13, B_14) | ~v1_relat_1('#skF_3'(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_248])).
% 3.82/1.70  tff(c_264, plain, (![A_13, B_14]: (k7_relat_1('#skF_3'(A_13, B_14), A_13)='#skF_3'(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_257])).
% 3.82/1.70  tff(c_1517, plain, (![A_1661, A_1662, B_1663]: (k7_relat_1('#skF_4'(A_1661), A_1662)='#skF_3'(A_1662, B_1663) | A_1662!='#skF_5' | A_1661!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_902, c_264])).
% 3.82/1.70  tff(c_234, plain, (![B_73]: (k7_relat_1(B_73, k1_relat_1(B_73))=B_73 | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_115, c_218])).
% 3.82/1.70  tff(c_1559, plain, (![A_1661, B_1663]: ('#skF_3'(k1_relat_1('#skF_4'(A_1661)), B_1663)='#skF_4'(A_1661) | ~v1_relat_1('#skF_4'(A_1661)) | k1_relat_1('#skF_4'(A_1661))!='#skF_5' | A_1661!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1517, c_234])).
% 3.82/1.70  tff(c_1635, plain, (![A_1664, B_1665]: ('#skF_4'(A_1664)='#skF_3'(A_1664, B_1665) | A_1664!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30, c_26, c_1559])).
% 3.82/1.70  tff(c_16, plain, (![A_13, B_14, D_19]: (k1_funct_1('#skF_3'(A_13, B_14), D_19)=B_14 | ~r2_hidden(D_19, A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.82/1.70  tff(c_2340, plain, (![A_1685, D_1686]: (k1_funct_1('#skF_4'(A_1685), D_1686)='#skF_5' | ~r2_hidden(D_1686, A_1685) | A_1685!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1635, c_16])).
% 3.82/1.70  tff(c_24, plain, (![A_20, C_25]: (k1_funct_1('#skF_4'(A_20), C_25)=k1_xboole_0 | ~r2_hidden(C_25, A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.82/1.70  tff(c_2343, plain, (![D_1686, A_1685]: (k1_xboole_0='#skF_5' | ~r2_hidden(D_1686, A_1685) | ~r2_hidden(D_1686, A_1685) | A_1685!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2340, c_24])).
% 3.82/1.70  tff(c_2448, plain, (![D_2403, A_2404]: (~r2_hidden(D_2403, A_2404) | ~r2_hidden(D_2403, A_2404) | A_2404!='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_32, c_2343])).
% 3.82/1.70  tff(c_2462, plain, (![A_2416]: (~r2_hidden('#skF_1'(A_2416), A_2416) | A_2416!='#skF_5' | v1_xboole_0(A_2416))), inference(resolution, [status(thm)], [c_4, c_2448])).
% 3.82/1.70  tff(c_2468, plain, (![B_60]: (B_60!='#skF_5' | ~r1_tarski(B_60, B_60) | v1_xboole_0(B_60))), inference(resolution, [status(thm)], [c_125, c_2462])).
% 3.82/1.70  tff(c_2477, plain, (![B_2428]: (B_2428!='#skF_5' | v1_xboole_0(B_2428))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_2468])).
% 3.82/1.70  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.82/1.70  tff(c_116, plain, (![A_54, B_55]: (~v1_xboole_0(A_54) | r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_107, c_2])).
% 3.82/1.70  tff(c_232, plain, (![A_20, A_74]: (k7_relat_1('#skF_4'(A_20), A_74)='#skF_4'(A_20) | ~r1_tarski(A_20, A_74) | ~v1_relat_1('#skF_4'(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_218])).
% 3.82/1.70  tff(c_362, plain, (![A_82, A_83]: (k7_relat_1('#skF_4'(A_82), A_83)='#skF_4'(A_82) | ~r1_tarski(A_82, A_83))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_232])).
% 3.82/1.70  tff(c_424, plain, (![A_84]: ('#skF_4'(A_84)=k1_xboole_0 | ~r1_tarski(A_84, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_82, c_362])).
% 3.82/1.70  tff(c_433, plain, (![A_54]: ('#skF_4'(A_54)=k1_xboole_0 | ~v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_116, c_424])).
% 3.82/1.70  tff(c_2490, plain, (![B_2440]: ('#skF_4'(B_2440)=k1_xboole_0 | B_2440!='#skF_5')), inference(resolution, [status(thm)], [c_2477, c_433])).
% 3.82/1.70  tff(c_2545, plain, (![B_2440]: (k1_relat_1(k1_xboole_0)=B_2440 | B_2440!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2490, c_26])).
% 3.82/1.70  tff(c_2585, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_319, c_2545])).
% 3.82/1.70  tff(c_2609, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2585, c_32])).
% 3.82/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.70  
% 3.82/1.70  Inference rules
% 3.82/1.70  ----------------------
% 3.82/1.70  #Ref     : 2
% 3.82/1.70  #Sup     : 703
% 3.82/1.70  #Fact    : 2
% 3.82/1.70  #Define  : 0
% 3.82/1.70  #Split   : 3
% 3.82/1.70  #Chain   : 0
% 3.82/1.70  #Close   : 0
% 3.82/1.70  
% 3.82/1.70  Ordering : KBO
% 3.82/1.70  
% 3.82/1.70  Simplification rules
% 3.82/1.70  ----------------------
% 3.82/1.70  #Subsume      : 262
% 3.82/1.70  #Demod        : 319
% 3.82/1.70  #Tautology    : 176
% 3.82/1.70  #SimpNegUnit  : 8
% 3.82/1.70  #BackRed      : 26
% 3.82/1.70  
% 3.82/1.70  #Partial instantiations: 1565
% 3.82/1.70  #Strategies tried      : 1
% 3.82/1.70  
% 3.82/1.70  Timing (in seconds)
% 3.82/1.70  ----------------------
% 3.82/1.70  Preprocessing        : 0.28
% 3.82/1.70  Parsing              : 0.15
% 3.82/1.70  CNF conversion       : 0.02
% 3.82/1.70  Main loop            : 0.64
% 3.82/1.70  Inferencing          : 0.26
% 3.82/1.70  Reduction            : 0.20
% 3.82/1.70  Demodulation         : 0.14
% 3.82/1.70  BG Simplification    : 0.03
% 3.82/1.70  Subsumption          : 0.12
% 3.82/1.70  Abstraction          : 0.03
% 3.82/1.70  MUC search           : 0.00
% 3.82/1.70  Cooper               : 0.00
% 3.82/1.70  Total                : 0.96
% 3.82/1.70  Index Insertion      : 0.00
% 3.82/1.70  Index Deletion       : 0.00
% 3.82/1.70  Index Matching       : 0.00
% 3.82/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
