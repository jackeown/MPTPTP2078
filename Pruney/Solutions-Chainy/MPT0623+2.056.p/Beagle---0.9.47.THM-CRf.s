%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:13 EST 2020

% Result     : Theorem 12.32s
% Output     : CNFRefutation 12.48s
% Verified   : 
% Statistics : Number of formulae       :  155 (1125 expanded)
%              Number of leaves         :   28 ( 410 expanded)
%              Depth                    :   25
%              Number of atoms          :  353 (3689 expanded)
%              Number of equality atoms :  105 (1296 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_11 > #skF_8 > #skF_3 > #skF_10 > #skF_5 > #skF_2 > #skF_1 > #skF_9 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_59,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_113,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_77,axiom,(
    ! [A] :
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(c_32,plain,(
    ! [A_46,B_47] : v1_relat_1('#skF_6'(A_46,B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    ! [A_46,B_47] : v1_funct_1('#skF_6'(A_46,B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    ! [A_46,B_47] : k1_relat_1('#skF_6'(A_46,B_47)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16319,plain,(
    ! [A_569,C_570] :
      ( r2_hidden('#skF_5'(A_569,k2_relat_1(A_569),C_570),k1_relat_1(A_569))
      | ~ r2_hidden(C_570,k2_relat_1(A_569))
      | ~ v1_funct_1(A_569)
      | ~ v1_relat_1(A_569) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_46,B_47,D_52] :
      ( k1_funct_1('#skF_6'(A_46,B_47),D_52) = B_47
      | ~ r2_hidden(D_52,A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16285,plain,(
    ! [A_557,D_558] :
      ( r2_hidden(k1_funct_1(A_557,D_558),k2_relat_1(A_557))
      | ~ r2_hidden(D_558,k1_relat_1(A_557))
      | ~ v1_funct_1(A_557)
      | ~ v1_relat_1(A_557) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16290,plain,(
    ! [B_47,A_46,D_52] :
      ( r2_hidden(B_47,k2_relat_1('#skF_6'(A_46,B_47)))
      | ~ r2_hidden(D_52,k1_relat_1('#skF_6'(A_46,B_47)))
      | ~ v1_funct_1('#skF_6'(A_46,B_47))
      | ~ v1_relat_1('#skF_6'(A_46,B_47))
      | ~ r2_hidden(D_52,A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_16285])).

tff(c_16293,plain,(
    ! [B_47,A_46,D_52] :
      ( r2_hidden(B_47,k2_relat_1('#skF_6'(A_46,B_47)))
      | ~ r2_hidden(D_52,A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_16290])).

tff(c_16434,plain,(
    ! [B_592,A_593,C_594] :
      ( r2_hidden(B_592,k2_relat_1('#skF_6'(k1_relat_1(A_593),B_592)))
      | ~ r2_hidden(C_594,k2_relat_1(A_593))
      | ~ v1_funct_1(A_593)
      | ~ v1_relat_1(A_593) ) ),
    inference(resolution,[status(thm)],[c_16319,c_16293])).

tff(c_16488,plain,(
    ! [B_598,A_599,B_600] :
      ( r2_hidden(B_598,k2_relat_1('#skF_6'(k1_relat_1(A_599),B_598)))
      | ~ v1_funct_1(A_599)
      | ~ v1_relat_1(A_599)
      | r1_tarski(k2_relat_1(A_599),B_600) ) ),
    inference(resolution,[status(thm)],[c_6,c_16434])).

tff(c_16514,plain,(
    ! [B_598,A_46,B_47,B_600] :
      ( r2_hidden(B_598,k2_relat_1('#skF_6'(A_46,B_598)))
      | ~ v1_funct_1('#skF_6'(A_46,B_47))
      | ~ v1_relat_1('#skF_6'(A_46,B_47))
      | r1_tarski(k2_relat_1('#skF_6'(A_46,B_47)),B_600) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_16488])).

tff(c_16529,plain,(
    ! [B_603,A_604,B_605,B_606] :
      ( r2_hidden(B_603,k2_relat_1('#skF_6'(A_604,B_603)))
      | r1_tarski(k2_relat_1('#skF_6'(A_604,B_605)),B_606) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_16514])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_11'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_55,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_36,plain,(
    ! [A_53] :
      ( k1_relat_1('#skF_8'(A_53)) = A_53
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_42,plain,(
    ! [A_53] :
      ( v1_relat_1('#skF_8'(A_53))
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_248,plain,(
    ! [A_127,C_128] :
      ( r2_hidden('#skF_5'(A_127,k2_relat_1(A_127),C_128),k1_relat_1(A_127))
      | ~ r2_hidden(C_128,k2_relat_1(A_127))
      | ~ v1_funct_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12402,plain,(
    ! [A_495,C_496] :
      ( r2_hidden('#skF_5'('#skF_8'(A_495),k2_relat_1('#skF_8'(A_495)),C_496),A_495)
      | ~ r2_hidden(C_496,k2_relat_1('#skF_8'(A_495)))
      | ~ v1_funct_1('#skF_8'(A_495))
      | ~ v1_relat_1('#skF_8'(A_495))
      | k1_xboole_0 = A_495 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_248])).

tff(c_265,plain,(
    ! [A_46,B_47,C_128] :
      ( r2_hidden('#skF_5'('#skF_6'(A_46,B_47),k2_relat_1('#skF_6'(A_46,B_47)),C_128),A_46)
      | ~ r2_hidden(C_128,k2_relat_1('#skF_6'(A_46,B_47)))
      | ~ v1_funct_1('#skF_6'(A_46,B_47))
      | ~ v1_relat_1('#skF_6'(A_46,B_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_248])).

tff(c_271,plain,(
    ! [A_46,B_47,C_128] :
      ( r2_hidden('#skF_5'('#skF_6'(A_46,B_47),k2_relat_1('#skF_6'(A_46,B_47)),C_128),A_46)
      | ~ r2_hidden(C_128,k2_relat_1('#skF_6'(A_46,B_47))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_265])).

tff(c_181,plain,(
    ! [A_114,C_115] :
      ( k1_funct_1(A_114,'#skF_5'(A_114,k2_relat_1(A_114),C_115)) = C_115
      | ~ r2_hidden(C_115,k2_relat_1(A_114))
      | ~ v1_funct_1(A_114)
      | ~ v1_relat_1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_198,plain,(
    ! [C_115,B_47,A_46] :
      ( C_115 = B_47
      | ~ r2_hidden(C_115,k2_relat_1('#skF_6'(A_46,B_47)))
      | ~ v1_funct_1('#skF_6'(A_46,B_47))
      | ~ v1_relat_1('#skF_6'(A_46,B_47))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_46,B_47),k2_relat_1('#skF_6'(A_46,B_47)),C_115),A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_181])).

tff(c_6923,plain,(
    ! [C_412,B_413,A_414] :
      ( C_412 = B_413
      | ~ r2_hidden(C_412,k2_relat_1('#skF_6'(A_414,B_413)))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_414,B_413),k2_relat_1('#skF_6'(A_414,B_413)),C_412),A_414) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_198])).

tff(c_6988,plain,(
    ! [C_415,B_416,A_417] :
      ( C_415 = B_416
      | ~ r2_hidden(C_415,k2_relat_1('#skF_6'(A_417,B_416))) ) ),
    inference(resolution,[status(thm)],[c_271,c_6923])).

tff(c_7288,plain,(
    ! [A_422,B_423,B_424] :
      ( '#skF_1'(k2_relat_1('#skF_6'(A_422,B_423)),B_424) = B_423
      | r1_tarski(k2_relat_1('#skF_6'(A_422,B_423)),B_424) ) ),
    inference(resolution,[status(thm)],[c_6,c_6988])).

tff(c_52,plain,(
    ! [C_65] :
      ( ~ r1_tarski(k2_relat_1(C_65),'#skF_10')
      | k1_relat_1(C_65) != '#skF_11'
      | ~ v1_funct_1(C_65)
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_7353,plain,(
    ! [A_422,B_423] :
      ( k1_relat_1('#skF_6'(A_422,B_423)) != '#skF_11'
      | ~ v1_funct_1('#skF_6'(A_422,B_423))
      | ~ v1_relat_1('#skF_6'(A_422,B_423))
      | '#skF_1'(k2_relat_1('#skF_6'(A_422,B_423)),'#skF_10') = B_423 ) ),
    inference(resolution,[status(thm)],[c_7288,c_52])).

tff(c_7412,plain,(
    ! [A_425,B_426] :
      ( A_425 != '#skF_11'
      | '#skF_1'(k2_relat_1('#skF_6'(A_425,B_426)),'#skF_10') = B_426 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_7353])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7461,plain,(
    ! [B_427,A_428] :
      ( ~ r2_hidden(B_427,'#skF_10')
      | r1_tarski(k2_relat_1('#skF_6'(A_428,B_427)),'#skF_10')
      | A_428 != '#skF_11' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7412,c_4])).

tff(c_7510,plain,(
    ! [A_428,B_427] :
      ( k1_relat_1('#skF_6'(A_428,B_427)) != '#skF_11'
      | ~ v1_funct_1('#skF_6'(A_428,B_427))
      | ~ v1_relat_1('#skF_6'(A_428,B_427))
      | ~ r2_hidden(B_427,'#skF_10')
      | A_428 != '#skF_11' ) ),
    inference(resolution,[status(thm)],[c_7461,c_52])).

tff(c_7562,plain,(
    ! [B_427,A_428] :
      ( ~ r2_hidden(B_427,'#skF_10')
      | A_428 != '#skF_11' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_7510])).

tff(c_7563,plain,(
    ! [A_428] : A_428 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_7562])).

tff(c_7567,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_7563])).

tff(c_7568,plain,(
    ! [B_427] : ~ r2_hidden(B_427,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_7562])).

tff(c_12423,plain,(
    ! [C_496] :
      ( ~ r2_hidden(C_496,k2_relat_1('#skF_8'('#skF_10')))
      | ~ v1_funct_1('#skF_8'('#skF_10'))
      | ~ v1_relat_1('#skF_8'('#skF_10'))
      | k1_xboole_0 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_12402,c_7568])).

tff(c_12476,plain,(
    ! [C_496] :
      ( ~ r2_hidden(C_496,k2_relat_1('#skF_8'('#skF_10')))
      | ~ v1_funct_1('#skF_8'('#skF_10'))
      | ~ v1_relat_1('#skF_8'('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_12423])).

tff(c_12493,plain,(
    ~ v1_relat_1('#skF_8'('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_12476])).

tff(c_12496,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_42,c_12493])).

tff(c_12500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_12496])).

tff(c_12502,plain,(
    v1_relat_1('#skF_8'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_12476])).

tff(c_40,plain,(
    ! [A_53] :
      ( v1_funct_1('#skF_8'(A_53))
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12501,plain,(
    ! [C_496] :
      ( ~ v1_funct_1('#skF_8'('#skF_10'))
      | ~ r2_hidden(C_496,k2_relat_1('#skF_8'('#skF_10'))) ) ),
    inference(splitRight,[status(thm)],[c_12476])).

tff(c_12510,plain,(
    ~ v1_funct_1('#skF_8'('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_12501])).

tff(c_12513,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_40,c_12510])).

tff(c_12517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_12513])).

tff(c_12519,plain,(
    v1_funct_1('#skF_8'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_12501])).

tff(c_934,plain,(
    ! [A_211,B_212] :
      ( r2_hidden('#skF_9'(A_211,B_212),k1_relat_1(A_211))
      | B_212 = A_211
      | k1_relat_1(B_212) != k1_relat_1(A_211)
      | ~ v1_funct_1(B_212)
      | ~ v1_relat_1(B_212)
      | ~ v1_funct_1(A_211)
      | ~ v1_relat_1(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_951,plain,(
    ! [A_46,B_47,B_212] :
      ( r2_hidden('#skF_9'('#skF_6'(A_46,B_47),B_212),A_46)
      | B_212 = '#skF_6'(A_46,B_47)
      | k1_relat_1(B_212) != k1_relat_1('#skF_6'(A_46,B_47))
      | ~ v1_funct_1(B_212)
      | ~ v1_relat_1(B_212)
      | ~ v1_funct_1('#skF_6'(A_46,B_47))
      | ~ v1_relat_1('#skF_6'(A_46,B_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_934])).

tff(c_1145,plain,(
    ! [A_236,B_237,B_238] :
      ( r2_hidden('#skF_9'('#skF_6'(A_236,B_237),B_238),A_236)
      | B_238 = '#skF_6'(A_236,B_237)
      | k1_relat_1(B_238) != A_236
      | ~ v1_funct_1(B_238)
      | ~ v1_relat_1(B_238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_951])).

tff(c_123,plain,(
    ! [A_94,D_95] :
      ( r2_hidden(k1_funct_1(A_94,D_95),k2_relat_1(A_94))
      | ~ r2_hidden(D_95,k1_relat_1(A_94))
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_128,plain,(
    ! [B_47,A_46,D_52] :
      ( r2_hidden(B_47,k2_relat_1('#skF_6'(A_46,B_47)))
      | ~ r2_hidden(D_52,k1_relat_1('#skF_6'(A_46,B_47)))
      | ~ v1_funct_1('#skF_6'(A_46,B_47))
      | ~ v1_relat_1('#skF_6'(A_46,B_47))
      | ~ r2_hidden(D_52,A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_123])).

tff(c_131,plain,(
    ! [B_47,A_46,D_52] :
      ( r2_hidden(B_47,k2_relat_1('#skF_6'(A_46,B_47)))
      | ~ r2_hidden(D_52,A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_128])).

tff(c_1173,plain,(
    ! [B_47,A_236,B_238,B_237] :
      ( r2_hidden(B_47,k2_relat_1('#skF_6'(A_236,B_47)))
      | B_238 = '#skF_6'(A_236,B_237)
      | k1_relat_1(B_238) != A_236
      | ~ v1_funct_1(B_238)
      | ~ v1_relat_1(B_238) ) ),
    inference(resolution,[status(thm)],[c_1145,c_131])).

tff(c_1234,plain,(
    ! [B_47,B_238,B_237] :
      ( r2_hidden(B_47,k2_relat_1('#skF_6'(k1_relat_1(B_238),B_47)))
      | '#skF_6'(k1_relat_1(B_238),B_237) = B_238
      | ~ v1_funct_1(B_238)
      | ~ v1_relat_1(B_238) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1173])).

tff(c_799,plain,(
    ! [A_199,B_200,C_201] :
      ( r2_hidden('#skF_5'('#skF_6'(A_199,B_200),k2_relat_1('#skF_6'(A_199,B_200)),C_201),A_199)
      | ~ r2_hidden(C_201,k2_relat_1('#skF_6'(A_199,B_200))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_265])).

tff(c_8,plain,(
    ! [A_6,D_45] :
      ( r2_hidden(k1_funct_1(A_6,D_45),k2_relat_1(A_6))
      | ~ r2_hidden(D_45,k1_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_132,plain,(
    ! [B_96,A_97,D_98] :
      ( r2_hidden(B_96,k2_relat_1('#skF_6'(A_97,B_96)))
      | ~ r2_hidden(D_98,A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_128])).

tff(c_139,plain,(
    ! [B_96,A_6,D_45] :
      ( r2_hidden(B_96,k2_relat_1('#skF_6'(k2_relat_1(A_6),B_96)))
      | ~ r2_hidden(D_45,k1_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_132])).

tff(c_2333,plain,(
    ! [B_266,A_267,C_268,B_269] :
      ( r2_hidden(B_266,k2_relat_1('#skF_6'(k2_relat_1(A_267),B_266)))
      | ~ v1_funct_1(A_267)
      | ~ v1_relat_1(A_267)
      | ~ r2_hidden(C_268,k2_relat_1('#skF_6'(k1_relat_1(A_267),B_269))) ) ),
    inference(resolution,[status(thm)],[c_799,c_139])).

tff(c_2397,plain,(
    ! [B_266,B_238,B_237] :
      ( r2_hidden(B_266,k2_relat_1('#skF_6'(k2_relat_1(B_238),B_266)))
      | '#skF_6'(k1_relat_1(B_238),B_237) = B_238
      | ~ v1_funct_1(B_238)
      | ~ v1_relat_1(B_238) ) ),
    inference(resolution,[status(thm)],[c_1234,c_2333])).

tff(c_12617,plain,(
    ! [C_499] : ~ r2_hidden(C_499,k2_relat_1('#skF_8'('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_12501])).

tff(c_12984,plain,(
    ! [C_505,B_506] : ~ r2_hidden(C_505,k2_relat_1('#skF_6'(k2_relat_1('#skF_8'('#skF_10')),B_506))) ),
    inference(resolution,[status(thm)],[c_271,c_12617])).

tff(c_13056,plain,(
    ! [B_237] :
      ( '#skF_6'(k1_relat_1('#skF_8'('#skF_10')),B_237) = '#skF_8'('#skF_10')
      | ~ v1_funct_1('#skF_8'('#skF_10'))
      | ~ v1_relat_1('#skF_8'('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_2397,c_12984])).

tff(c_13174,plain,(
    ! [B_507] : '#skF_6'(k1_relat_1('#skF_8'('#skF_10')),B_507) = '#skF_8'('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12502,c_12519,c_13056])).

tff(c_13446,plain,(
    ! [B_507] :
      ( '#skF_6'('#skF_10',B_507) = '#skF_8'('#skF_10')
      | k1_xboole_0 = '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_13174])).

tff(c_13599,plain,(
    ! [B_507] : '#skF_6'('#skF_10',B_507) = '#skF_8'('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_13446])).

tff(c_957,plain,(
    ! [A_46,B_47,B_212] :
      ( r2_hidden('#skF_9'('#skF_6'(A_46,B_47),B_212),A_46)
      | B_212 = '#skF_6'(A_46,B_47)
      | k1_relat_1(B_212) != A_46
      | ~ v1_funct_1(B_212)
      | ~ v1_relat_1(B_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_951])).

tff(c_7569,plain,(
    ! [B_429] : ~ r2_hidden(B_429,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_7562])).

tff(c_9354,plain,(
    ! [B_460,B_461] :
      ( B_460 = '#skF_6'('#skF_10',B_461)
      | k1_relat_1(B_460) != '#skF_10'
      | ~ v1_funct_1(B_460)
      | ~ v1_relat_1(B_460) ) ),
    inference(resolution,[status(thm)],[c_957,c_7569])).

tff(c_9360,plain,(
    ! [A_46,B_47,B_461] :
      ( '#skF_6'(A_46,B_47) = '#skF_6'('#skF_10',B_461)
      | k1_relat_1('#skF_6'(A_46,B_47)) != '#skF_10'
      | ~ v1_funct_1('#skF_6'(A_46,B_47)) ) ),
    inference(resolution,[status(thm)],[c_32,c_9354])).

tff(c_9365,plain,(
    ! [A_46,B_47,B_461] :
      ( '#skF_6'(A_46,B_47) = '#skF_6'('#skF_10',B_461)
      | A_46 != '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_9360])).

tff(c_14219,plain,(
    ! [B_47] : '#skF_6'('#skF_10',B_47) = '#skF_8'('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13599,c_9365])).

tff(c_38,plain,(
    ! [A_53] :
      ( k1_relat_1('#skF_7'(A_53)) = A_53
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_46,plain,(
    ! [A_53] :
      ( v1_relat_1('#skF_7'(A_53))
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12526,plain,(
    ! [A_497,C_498] :
      ( r2_hidden('#skF_5'('#skF_7'(A_497),k2_relat_1('#skF_7'(A_497)),C_498),A_497)
      | ~ r2_hidden(C_498,k2_relat_1('#skF_7'(A_497)))
      | ~ v1_funct_1('#skF_7'(A_497))
      | ~ v1_relat_1('#skF_7'(A_497))
      | k1_xboole_0 = A_497 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_248])).

tff(c_12547,plain,(
    ! [C_498] :
      ( ~ r2_hidden(C_498,k2_relat_1('#skF_7'('#skF_10')))
      | ~ v1_funct_1('#skF_7'('#skF_10'))
      | ~ v1_relat_1('#skF_7'('#skF_10'))
      | k1_xboole_0 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_12526,c_7568])).

tff(c_12600,plain,(
    ! [C_498] :
      ( ~ r2_hidden(C_498,k2_relat_1('#skF_7'('#skF_10')))
      | ~ v1_funct_1('#skF_7'('#skF_10'))
      | ~ v1_relat_1('#skF_7'('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_12547])).

tff(c_14889,plain,(
    ~ v1_relat_1('#skF_7'('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_12600])).

tff(c_14892,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_46,c_14889])).

tff(c_14896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_14892])).

tff(c_14898,plain,(
    v1_relat_1('#skF_7'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_12600])).

tff(c_44,plain,(
    ! [A_53] :
      ( v1_funct_1('#skF_7'(A_53))
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14897,plain,(
    ! [C_498] :
      ( ~ v1_funct_1('#skF_7'('#skF_10'))
      | ~ r2_hidden(C_498,k2_relat_1('#skF_7'('#skF_10'))) ) ),
    inference(splitRight,[status(thm)],[c_12600])).

tff(c_14903,plain,(
    ~ v1_funct_1('#skF_7'('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_14897])).

tff(c_14906,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_44,c_14903])).

tff(c_14910,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_14906])).

tff(c_14912,plain,(
    v1_funct_1('#skF_7'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_14897])).

tff(c_15090,plain,(
    ! [C_520] : ~ r2_hidden(C_520,k2_relat_1('#skF_7'('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_14897])).

tff(c_15497,plain,(
    ! [C_526,B_527] : ~ r2_hidden(C_526,k2_relat_1('#skF_6'(k2_relat_1('#skF_7'('#skF_10')),B_527))) ),
    inference(resolution,[status(thm)],[c_271,c_15090])).

tff(c_15585,plain,(
    ! [B_237] :
      ( '#skF_6'(k1_relat_1('#skF_7'('#skF_10')),B_237) = '#skF_7'('#skF_10')
      | ~ v1_funct_1('#skF_7'('#skF_10'))
      | ~ v1_relat_1('#skF_7'('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_2397,c_15497])).

tff(c_15707,plain,(
    ! [B_528] : '#skF_6'(k1_relat_1('#skF_7'('#skF_10')),B_528) = '#skF_7'('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14898,c_14912,c_15585])).

tff(c_15979,plain,(
    ! [B_528] :
      ( '#skF_7'('#skF_10') = '#skF_6'('#skF_10',B_528)
      | k1_xboole_0 = '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_15707])).

tff(c_16132,plain,
    ( '#skF_7'('#skF_10') = '#skF_8'('#skF_10')
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14219,c_15979])).

tff(c_16133,plain,(
    '#skF_7'('#skF_10') = '#skF_8'('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_16132])).

tff(c_34,plain,(
    ! [A_53] :
      ( '#skF_7'(A_53) != '#skF_8'(A_53)
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16167,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_16133,c_34])).

tff(c_16194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_16167])).

tff(c_16196,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_16195,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_16201,plain,(
    '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16196,c_16195])).

tff(c_16211,plain,(
    ! [C_65] :
      ( ~ r1_tarski(k2_relat_1(C_65),'#skF_10')
      | k1_relat_1(C_65) != '#skF_10'
      | ~ v1_funct_1(C_65)
      | ~ v1_relat_1(C_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16201,c_52])).

tff(c_16547,plain,(
    ! [A_604,B_605,B_603] :
      ( k1_relat_1('#skF_6'(A_604,B_605)) != '#skF_10'
      | ~ v1_funct_1('#skF_6'(A_604,B_605))
      | ~ v1_relat_1('#skF_6'(A_604,B_605))
      | r2_hidden(B_603,k2_relat_1('#skF_6'(A_604,B_603))) ) ),
    inference(resolution,[status(thm)],[c_16529,c_16211])).

tff(c_16559,plain,(
    ! [A_604,B_603] :
      ( A_604 != '#skF_10'
      | r2_hidden(B_603,k2_relat_1('#skF_6'(A_604,B_603))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_16547])).

tff(c_16332,plain,(
    ! [A_46,B_47,C_570] :
      ( r2_hidden('#skF_5'('#skF_6'(A_46,B_47),k2_relat_1('#skF_6'(A_46,B_47)),C_570),A_46)
      | ~ r2_hidden(C_570,k2_relat_1('#skF_6'(A_46,B_47)))
      | ~ v1_funct_1('#skF_6'(A_46,B_47))
      | ~ v1_relat_1('#skF_6'(A_46,B_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_16319])).

tff(c_16336,plain,(
    ! [A_46,B_47,C_570] :
      ( r2_hidden('#skF_5'('#skF_6'(A_46,B_47),k2_relat_1('#skF_6'(A_46,B_47)),C_570),A_46)
      | ~ r2_hidden(C_570,k2_relat_1('#skF_6'(A_46,B_47))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_16332])).

tff(c_16256,plain,(
    ! [A_545,B_546] :
      ( ~ r2_hidden('#skF_1'(A_545,B_546),B_546)
      | r1_tarski(A_545,B_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16261,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_16256])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16334,plain,(
    ! [A_569,C_570,B_2] :
      ( r2_hidden('#skF_5'(A_569,k2_relat_1(A_569),C_570),B_2)
      | ~ r1_tarski(k1_relat_1(A_569),B_2)
      | ~ r2_hidden(C_570,k2_relat_1(A_569))
      | ~ v1_funct_1(A_569)
      | ~ v1_relat_1(A_569) ) ),
    inference(resolution,[status(thm)],[c_16319,c_2])).

tff(c_16410,plain,(
    ! [A_590,C_591] :
      ( k1_funct_1(A_590,'#skF_5'(A_590,k2_relat_1(A_590),C_591)) = C_591
      | ~ r2_hidden(C_591,k2_relat_1(A_590))
      | ~ v1_funct_1(A_590)
      | ~ v1_relat_1(A_590) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16420,plain,(
    ! [C_591,B_47,A_46] :
      ( C_591 = B_47
      | ~ r2_hidden('#skF_5'('#skF_6'(A_46,B_47),k2_relat_1('#skF_6'(A_46,B_47)),C_591),A_46)
      | ~ r2_hidden(C_591,k2_relat_1('#skF_6'(A_46,B_47)))
      | ~ v1_funct_1('#skF_6'(A_46,B_47))
      | ~ v1_relat_1('#skF_6'(A_46,B_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16410,c_26])).

tff(c_23177,plain,(
    ! [C_881,B_882,A_883] :
      ( C_881 = B_882
      | ~ r2_hidden('#skF_5'('#skF_6'(A_883,B_882),k2_relat_1('#skF_6'(A_883,B_882)),C_881),A_883)
      | ~ r2_hidden(C_881,k2_relat_1('#skF_6'(A_883,B_882))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_16420])).

tff(c_23181,plain,(
    ! [C_570,B_882,B_2] :
      ( C_570 = B_882
      | ~ r1_tarski(k1_relat_1('#skF_6'(B_2,B_882)),B_2)
      | ~ r2_hidden(C_570,k2_relat_1('#skF_6'(B_2,B_882)))
      | ~ v1_funct_1('#skF_6'(B_2,B_882))
      | ~ v1_relat_1('#skF_6'(B_2,B_882)) ) ),
    inference(resolution,[status(thm)],[c_16334,c_23177])).

tff(c_23249,plain,(
    ! [C_884,B_885,B_886] :
      ( C_884 = B_885
      | ~ r2_hidden(C_884,k2_relat_1('#skF_6'(B_886,B_885))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_16261,c_28,c_23181])).

tff(c_23706,plain,(
    ! [B_895,B_896,B_897] :
      ( '#skF_1'(k2_relat_1('#skF_6'(B_895,B_896)),B_897) = B_896
      | r1_tarski(k2_relat_1('#skF_6'(B_895,B_896)),B_897) ) ),
    inference(resolution,[status(thm)],[c_6,c_23249])).

tff(c_23773,plain,(
    ! [B_895,B_896] :
      ( k1_relat_1('#skF_6'(B_895,B_896)) != '#skF_10'
      | ~ v1_funct_1('#skF_6'(B_895,B_896))
      | ~ v1_relat_1('#skF_6'(B_895,B_896))
      | '#skF_1'(k2_relat_1('#skF_6'(B_895,B_896)),'#skF_10') = B_896 ) ),
    inference(resolution,[status(thm)],[c_23706,c_16211])).

tff(c_23833,plain,(
    ! [B_898,B_899] :
      ( B_898 != '#skF_10'
      | '#skF_1'(k2_relat_1('#skF_6'(B_898,B_899)),'#skF_10') = B_899 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_23773])).

tff(c_23882,plain,(
    ! [B_900,B_901] :
      ( ~ r2_hidden(B_900,'#skF_10')
      | r1_tarski(k2_relat_1('#skF_6'(B_901,B_900)),'#skF_10')
      | B_901 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23833,c_4])).

tff(c_23933,plain,(
    ! [B_901,B_900] :
      ( k1_relat_1('#skF_6'(B_901,B_900)) != '#skF_10'
      | ~ v1_funct_1('#skF_6'(B_901,B_900))
      | ~ v1_relat_1('#skF_6'(B_901,B_900))
      | ~ r2_hidden(B_900,'#skF_10')
      | B_901 != '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_23882,c_16211])).

tff(c_23989,plain,(
    ! [B_900,B_901] :
      ( ~ r2_hidden(B_900,'#skF_10')
      | B_901 != '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_23933])).

tff(c_23990,plain,(
    ! [B_901] : B_901 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_23989])).

tff(c_24002,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23990,c_16201])).

tff(c_24179,plain,(
    ! [B_905] : ~ r2_hidden(B_905,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_23989])).

tff(c_24264,plain,(
    ! [C_907,B_908] : ~ r2_hidden(C_907,k2_relat_1('#skF_6'('#skF_10',B_908))) ),
    inference(resolution,[status(thm)],[c_16336,c_24179])).

tff(c_24392,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_16559,c_24264])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:42:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.32/4.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.32/4.33  
% 12.32/4.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.32/4.33  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_11 > #skF_8 > #skF_3 > #skF_10 > #skF_5 > #skF_2 > #skF_1 > #skF_9 > #skF_4
% 12.32/4.33  
% 12.32/4.33  %Foreground sorts:
% 12.32/4.33  
% 12.32/4.33  
% 12.32/4.33  %Background operators:
% 12.32/4.33  
% 12.32/4.33  
% 12.32/4.33  %Foreground operators:
% 12.32/4.33  tff('#skF_7', type, '#skF_7': $i > $i).
% 12.32/4.33  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 12.32/4.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.32/4.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.32/4.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.32/4.33  tff('#skF_11', type, '#skF_11': $i).
% 12.32/4.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.32/4.33  tff('#skF_8', type, '#skF_8': $i > $i).
% 12.32/4.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.32/4.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.32/4.33  tff('#skF_10', type, '#skF_10': $i).
% 12.32/4.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.32/4.33  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 12.32/4.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.32/4.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.32/4.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.32/4.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.32/4.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.32/4.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.32/4.33  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 12.32/4.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.32/4.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.32/4.33  
% 12.48/4.36  tff(f_59, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 12.48/4.36  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 12.48/4.36  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 12.48/4.36  tff(f_113, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 12.48/4.36  tff(f_77, axiom, (![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 12.48/4.36  tff(f_95, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 12.48/4.36  tff(c_32, plain, (![A_46, B_47]: (v1_relat_1('#skF_6'(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.48/4.36  tff(c_30, plain, (![A_46, B_47]: (v1_funct_1('#skF_6'(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.48/4.36  tff(c_28, plain, (![A_46, B_47]: (k1_relat_1('#skF_6'(A_46, B_47))=A_46)), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.48/4.36  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.48/4.36  tff(c_16319, plain, (![A_569, C_570]: (r2_hidden('#skF_5'(A_569, k2_relat_1(A_569), C_570), k1_relat_1(A_569)) | ~r2_hidden(C_570, k2_relat_1(A_569)) | ~v1_funct_1(A_569) | ~v1_relat_1(A_569))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.48/4.36  tff(c_26, plain, (![A_46, B_47, D_52]: (k1_funct_1('#skF_6'(A_46, B_47), D_52)=B_47 | ~r2_hidden(D_52, A_46))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.48/4.36  tff(c_16285, plain, (![A_557, D_558]: (r2_hidden(k1_funct_1(A_557, D_558), k2_relat_1(A_557)) | ~r2_hidden(D_558, k1_relat_1(A_557)) | ~v1_funct_1(A_557) | ~v1_relat_1(A_557))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.48/4.36  tff(c_16290, plain, (![B_47, A_46, D_52]: (r2_hidden(B_47, k2_relat_1('#skF_6'(A_46, B_47))) | ~r2_hidden(D_52, k1_relat_1('#skF_6'(A_46, B_47))) | ~v1_funct_1('#skF_6'(A_46, B_47)) | ~v1_relat_1('#skF_6'(A_46, B_47)) | ~r2_hidden(D_52, A_46))), inference(superposition, [status(thm), theory('equality')], [c_26, c_16285])).
% 12.48/4.36  tff(c_16293, plain, (![B_47, A_46, D_52]: (r2_hidden(B_47, k2_relat_1('#skF_6'(A_46, B_47))) | ~r2_hidden(D_52, A_46))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_16290])).
% 12.48/4.36  tff(c_16434, plain, (![B_592, A_593, C_594]: (r2_hidden(B_592, k2_relat_1('#skF_6'(k1_relat_1(A_593), B_592))) | ~r2_hidden(C_594, k2_relat_1(A_593)) | ~v1_funct_1(A_593) | ~v1_relat_1(A_593))), inference(resolution, [status(thm)], [c_16319, c_16293])).
% 12.48/4.36  tff(c_16488, plain, (![B_598, A_599, B_600]: (r2_hidden(B_598, k2_relat_1('#skF_6'(k1_relat_1(A_599), B_598))) | ~v1_funct_1(A_599) | ~v1_relat_1(A_599) | r1_tarski(k2_relat_1(A_599), B_600))), inference(resolution, [status(thm)], [c_6, c_16434])).
% 12.48/4.36  tff(c_16514, plain, (![B_598, A_46, B_47, B_600]: (r2_hidden(B_598, k2_relat_1('#skF_6'(A_46, B_598))) | ~v1_funct_1('#skF_6'(A_46, B_47)) | ~v1_relat_1('#skF_6'(A_46, B_47)) | r1_tarski(k2_relat_1('#skF_6'(A_46, B_47)), B_600))), inference(superposition, [status(thm), theory('equality')], [c_28, c_16488])).
% 12.48/4.36  tff(c_16529, plain, (![B_603, A_604, B_605, B_606]: (r2_hidden(B_603, k2_relat_1('#skF_6'(A_604, B_603))) | r1_tarski(k2_relat_1('#skF_6'(A_604, B_605)), B_606))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_16514])).
% 12.48/4.36  tff(c_54, plain, (k1_xboole_0='#skF_11' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_113])).
% 12.48/4.36  tff(c_55, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_54])).
% 12.48/4.36  tff(c_36, plain, (![A_53]: (k1_relat_1('#skF_8'(A_53))=A_53 | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.48/4.36  tff(c_42, plain, (![A_53]: (v1_relat_1('#skF_8'(A_53)) | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.48/4.36  tff(c_248, plain, (![A_127, C_128]: (r2_hidden('#skF_5'(A_127, k2_relat_1(A_127), C_128), k1_relat_1(A_127)) | ~r2_hidden(C_128, k2_relat_1(A_127)) | ~v1_funct_1(A_127) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.48/4.36  tff(c_12402, plain, (![A_495, C_496]: (r2_hidden('#skF_5'('#skF_8'(A_495), k2_relat_1('#skF_8'(A_495)), C_496), A_495) | ~r2_hidden(C_496, k2_relat_1('#skF_8'(A_495))) | ~v1_funct_1('#skF_8'(A_495)) | ~v1_relat_1('#skF_8'(A_495)) | k1_xboole_0=A_495)), inference(superposition, [status(thm), theory('equality')], [c_36, c_248])).
% 12.48/4.36  tff(c_265, plain, (![A_46, B_47, C_128]: (r2_hidden('#skF_5'('#skF_6'(A_46, B_47), k2_relat_1('#skF_6'(A_46, B_47)), C_128), A_46) | ~r2_hidden(C_128, k2_relat_1('#skF_6'(A_46, B_47))) | ~v1_funct_1('#skF_6'(A_46, B_47)) | ~v1_relat_1('#skF_6'(A_46, B_47)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_248])).
% 12.48/4.36  tff(c_271, plain, (![A_46, B_47, C_128]: (r2_hidden('#skF_5'('#skF_6'(A_46, B_47), k2_relat_1('#skF_6'(A_46, B_47)), C_128), A_46) | ~r2_hidden(C_128, k2_relat_1('#skF_6'(A_46, B_47))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_265])).
% 12.48/4.36  tff(c_181, plain, (![A_114, C_115]: (k1_funct_1(A_114, '#skF_5'(A_114, k2_relat_1(A_114), C_115))=C_115 | ~r2_hidden(C_115, k2_relat_1(A_114)) | ~v1_funct_1(A_114) | ~v1_relat_1(A_114))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.48/4.36  tff(c_198, plain, (![C_115, B_47, A_46]: (C_115=B_47 | ~r2_hidden(C_115, k2_relat_1('#skF_6'(A_46, B_47))) | ~v1_funct_1('#skF_6'(A_46, B_47)) | ~v1_relat_1('#skF_6'(A_46, B_47)) | ~r2_hidden('#skF_5'('#skF_6'(A_46, B_47), k2_relat_1('#skF_6'(A_46, B_47)), C_115), A_46))), inference(superposition, [status(thm), theory('equality')], [c_26, c_181])).
% 12.48/4.36  tff(c_6923, plain, (![C_412, B_413, A_414]: (C_412=B_413 | ~r2_hidden(C_412, k2_relat_1('#skF_6'(A_414, B_413))) | ~r2_hidden('#skF_5'('#skF_6'(A_414, B_413), k2_relat_1('#skF_6'(A_414, B_413)), C_412), A_414))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_198])).
% 12.48/4.36  tff(c_6988, plain, (![C_415, B_416, A_417]: (C_415=B_416 | ~r2_hidden(C_415, k2_relat_1('#skF_6'(A_417, B_416))))), inference(resolution, [status(thm)], [c_271, c_6923])).
% 12.48/4.36  tff(c_7288, plain, (![A_422, B_423, B_424]: ('#skF_1'(k2_relat_1('#skF_6'(A_422, B_423)), B_424)=B_423 | r1_tarski(k2_relat_1('#skF_6'(A_422, B_423)), B_424))), inference(resolution, [status(thm)], [c_6, c_6988])).
% 12.48/4.36  tff(c_52, plain, (![C_65]: (~r1_tarski(k2_relat_1(C_65), '#skF_10') | k1_relat_1(C_65)!='#skF_11' | ~v1_funct_1(C_65) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_113])).
% 12.48/4.36  tff(c_7353, plain, (![A_422, B_423]: (k1_relat_1('#skF_6'(A_422, B_423))!='#skF_11' | ~v1_funct_1('#skF_6'(A_422, B_423)) | ~v1_relat_1('#skF_6'(A_422, B_423)) | '#skF_1'(k2_relat_1('#skF_6'(A_422, B_423)), '#skF_10')=B_423)), inference(resolution, [status(thm)], [c_7288, c_52])).
% 12.48/4.36  tff(c_7412, plain, (![A_425, B_426]: (A_425!='#skF_11' | '#skF_1'(k2_relat_1('#skF_6'(A_425, B_426)), '#skF_10')=B_426)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_7353])).
% 12.48/4.36  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.48/4.36  tff(c_7461, plain, (![B_427, A_428]: (~r2_hidden(B_427, '#skF_10') | r1_tarski(k2_relat_1('#skF_6'(A_428, B_427)), '#skF_10') | A_428!='#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_7412, c_4])).
% 12.48/4.36  tff(c_7510, plain, (![A_428, B_427]: (k1_relat_1('#skF_6'(A_428, B_427))!='#skF_11' | ~v1_funct_1('#skF_6'(A_428, B_427)) | ~v1_relat_1('#skF_6'(A_428, B_427)) | ~r2_hidden(B_427, '#skF_10') | A_428!='#skF_11')), inference(resolution, [status(thm)], [c_7461, c_52])).
% 12.48/4.36  tff(c_7562, plain, (![B_427, A_428]: (~r2_hidden(B_427, '#skF_10') | A_428!='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_7510])).
% 12.48/4.36  tff(c_7563, plain, (![A_428]: (A_428!='#skF_11')), inference(splitLeft, [status(thm)], [c_7562])).
% 12.48/4.36  tff(c_7567, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_7563])).
% 12.48/4.36  tff(c_7568, plain, (![B_427]: (~r2_hidden(B_427, '#skF_10'))), inference(splitRight, [status(thm)], [c_7562])).
% 12.48/4.36  tff(c_12423, plain, (![C_496]: (~r2_hidden(C_496, k2_relat_1('#skF_8'('#skF_10'))) | ~v1_funct_1('#skF_8'('#skF_10')) | ~v1_relat_1('#skF_8'('#skF_10')) | k1_xboole_0='#skF_10')), inference(resolution, [status(thm)], [c_12402, c_7568])).
% 12.48/4.36  tff(c_12476, plain, (![C_496]: (~r2_hidden(C_496, k2_relat_1('#skF_8'('#skF_10'))) | ~v1_funct_1('#skF_8'('#skF_10')) | ~v1_relat_1('#skF_8'('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_55, c_12423])).
% 12.48/4.36  tff(c_12493, plain, (~v1_relat_1('#skF_8'('#skF_10'))), inference(splitLeft, [status(thm)], [c_12476])).
% 12.48/4.36  tff(c_12496, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_42, c_12493])).
% 12.48/4.36  tff(c_12500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_12496])).
% 12.48/4.36  tff(c_12502, plain, (v1_relat_1('#skF_8'('#skF_10'))), inference(splitRight, [status(thm)], [c_12476])).
% 12.48/4.36  tff(c_40, plain, (![A_53]: (v1_funct_1('#skF_8'(A_53)) | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.48/4.36  tff(c_12501, plain, (![C_496]: (~v1_funct_1('#skF_8'('#skF_10')) | ~r2_hidden(C_496, k2_relat_1('#skF_8'('#skF_10'))))), inference(splitRight, [status(thm)], [c_12476])).
% 12.48/4.36  tff(c_12510, plain, (~v1_funct_1('#skF_8'('#skF_10'))), inference(splitLeft, [status(thm)], [c_12501])).
% 12.48/4.36  tff(c_12513, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_40, c_12510])).
% 12.48/4.36  tff(c_12517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_12513])).
% 12.48/4.36  tff(c_12519, plain, (v1_funct_1('#skF_8'('#skF_10'))), inference(splitRight, [status(thm)], [c_12501])).
% 12.48/4.36  tff(c_934, plain, (![A_211, B_212]: (r2_hidden('#skF_9'(A_211, B_212), k1_relat_1(A_211)) | B_212=A_211 | k1_relat_1(B_212)!=k1_relat_1(A_211) | ~v1_funct_1(B_212) | ~v1_relat_1(B_212) | ~v1_funct_1(A_211) | ~v1_relat_1(A_211))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.48/4.36  tff(c_951, plain, (![A_46, B_47, B_212]: (r2_hidden('#skF_9'('#skF_6'(A_46, B_47), B_212), A_46) | B_212='#skF_6'(A_46, B_47) | k1_relat_1(B_212)!=k1_relat_1('#skF_6'(A_46, B_47)) | ~v1_funct_1(B_212) | ~v1_relat_1(B_212) | ~v1_funct_1('#skF_6'(A_46, B_47)) | ~v1_relat_1('#skF_6'(A_46, B_47)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_934])).
% 12.48/4.36  tff(c_1145, plain, (![A_236, B_237, B_238]: (r2_hidden('#skF_9'('#skF_6'(A_236, B_237), B_238), A_236) | B_238='#skF_6'(A_236, B_237) | k1_relat_1(B_238)!=A_236 | ~v1_funct_1(B_238) | ~v1_relat_1(B_238))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_951])).
% 12.48/4.36  tff(c_123, plain, (![A_94, D_95]: (r2_hidden(k1_funct_1(A_94, D_95), k2_relat_1(A_94)) | ~r2_hidden(D_95, k1_relat_1(A_94)) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.48/4.36  tff(c_128, plain, (![B_47, A_46, D_52]: (r2_hidden(B_47, k2_relat_1('#skF_6'(A_46, B_47))) | ~r2_hidden(D_52, k1_relat_1('#skF_6'(A_46, B_47))) | ~v1_funct_1('#skF_6'(A_46, B_47)) | ~v1_relat_1('#skF_6'(A_46, B_47)) | ~r2_hidden(D_52, A_46))), inference(superposition, [status(thm), theory('equality')], [c_26, c_123])).
% 12.48/4.36  tff(c_131, plain, (![B_47, A_46, D_52]: (r2_hidden(B_47, k2_relat_1('#skF_6'(A_46, B_47))) | ~r2_hidden(D_52, A_46))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_128])).
% 12.48/4.36  tff(c_1173, plain, (![B_47, A_236, B_238, B_237]: (r2_hidden(B_47, k2_relat_1('#skF_6'(A_236, B_47))) | B_238='#skF_6'(A_236, B_237) | k1_relat_1(B_238)!=A_236 | ~v1_funct_1(B_238) | ~v1_relat_1(B_238))), inference(resolution, [status(thm)], [c_1145, c_131])).
% 12.48/4.36  tff(c_1234, plain, (![B_47, B_238, B_237]: (r2_hidden(B_47, k2_relat_1('#skF_6'(k1_relat_1(B_238), B_47))) | '#skF_6'(k1_relat_1(B_238), B_237)=B_238 | ~v1_funct_1(B_238) | ~v1_relat_1(B_238))), inference(reflexivity, [status(thm), theory('equality')], [c_1173])).
% 12.48/4.36  tff(c_799, plain, (![A_199, B_200, C_201]: (r2_hidden('#skF_5'('#skF_6'(A_199, B_200), k2_relat_1('#skF_6'(A_199, B_200)), C_201), A_199) | ~r2_hidden(C_201, k2_relat_1('#skF_6'(A_199, B_200))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_265])).
% 12.48/4.36  tff(c_8, plain, (![A_6, D_45]: (r2_hidden(k1_funct_1(A_6, D_45), k2_relat_1(A_6)) | ~r2_hidden(D_45, k1_relat_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.48/4.36  tff(c_132, plain, (![B_96, A_97, D_98]: (r2_hidden(B_96, k2_relat_1('#skF_6'(A_97, B_96))) | ~r2_hidden(D_98, A_97))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_128])).
% 12.48/4.36  tff(c_139, plain, (![B_96, A_6, D_45]: (r2_hidden(B_96, k2_relat_1('#skF_6'(k2_relat_1(A_6), B_96))) | ~r2_hidden(D_45, k1_relat_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_8, c_132])).
% 12.48/4.36  tff(c_2333, plain, (![B_266, A_267, C_268, B_269]: (r2_hidden(B_266, k2_relat_1('#skF_6'(k2_relat_1(A_267), B_266))) | ~v1_funct_1(A_267) | ~v1_relat_1(A_267) | ~r2_hidden(C_268, k2_relat_1('#skF_6'(k1_relat_1(A_267), B_269))))), inference(resolution, [status(thm)], [c_799, c_139])).
% 12.48/4.36  tff(c_2397, plain, (![B_266, B_238, B_237]: (r2_hidden(B_266, k2_relat_1('#skF_6'(k2_relat_1(B_238), B_266))) | '#skF_6'(k1_relat_1(B_238), B_237)=B_238 | ~v1_funct_1(B_238) | ~v1_relat_1(B_238))), inference(resolution, [status(thm)], [c_1234, c_2333])).
% 12.48/4.36  tff(c_12617, plain, (![C_499]: (~r2_hidden(C_499, k2_relat_1('#skF_8'('#skF_10'))))), inference(splitRight, [status(thm)], [c_12501])).
% 12.48/4.36  tff(c_12984, plain, (![C_505, B_506]: (~r2_hidden(C_505, k2_relat_1('#skF_6'(k2_relat_1('#skF_8'('#skF_10')), B_506))))), inference(resolution, [status(thm)], [c_271, c_12617])).
% 12.48/4.36  tff(c_13056, plain, (![B_237]: ('#skF_6'(k1_relat_1('#skF_8'('#skF_10')), B_237)='#skF_8'('#skF_10') | ~v1_funct_1('#skF_8'('#skF_10')) | ~v1_relat_1('#skF_8'('#skF_10')))), inference(resolution, [status(thm)], [c_2397, c_12984])).
% 12.48/4.36  tff(c_13174, plain, (![B_507]: ('#skF_6'(k1_relat_1('#skF_8'('#skF_10')), B_507)='#skF_8'('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_12502, c_12519, c_13056])).
% 12.48/4.36  tff(c_13446, plain, (![B_507]: ('#skF_6'('#skF_10', B_507)='#skF_8'('#skF_10') | k1_xboole_0='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_36, c_13174])).
% 12.48/4.36  tff(c_13599, plain, (![B_507]: ('#skF_6'('#skF_10', B_507)='#skF_8'('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_55, c_13446])).
% 12.48/4.36  tff(c_957, plain, (![A_46, B_47, B_212]: (r2_hidden('#skF_9'('#skF_6'(A_46, B_47), B_212), A_46) | B_212='#skF_6'(A_46, B_47) | k1_relat_1(B_212)!=A_46 | ~v1_funct_1(B_212) | ~v1_relat_1(B_212))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_951])).
% 12.48/4.36  tff(c_7569, plain, (![B_429]: (~r2_hidden(B_429, '#skF_10'))), inference(splitRight, [status(thm)], [c_7562])).
% 12.48/4.36  tff(c_9354, plain, (![B_460, B_461]: (B_460='#skF_6'('#skF_10', B_461) | k1_relat_1(B_460)!='#skF_10' | ~v1_funct_1(B_460) | ~v1_relat_1(B_460))), inference(resolution, [status(thm)], [c_957, c_7569])).
% 12.48/4.36  tff(c_9360, plain, (![A_46, B_47, B_461]: ('#skF_6'(A_46, B_47)='#skF_6'('#skF_10', B_461) | k1_relat_1('#skF_6'(A_46, B_47))!='#skF_10' | ~v1_funct_1('#skF_6'(A_46, B_47)))), inference(resolution, [status(thm)], [c_32, c_9354])).
% 12.48/4.36  tff(c_9365, plain, (![A_46, B_47, B_461]: ('#skF_6'(A_46, B_47)='#skF_6'('#skF_10', B_461) | A_46!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_9360])).
% 12.48/4.36  tff(c_14219, plain, (![B_47]: ('#skF_6'('#skF_10', B_47)='#skF_8'('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_13599, c_9365])).
% 12.48/4.36  tff(c_38, plain, (![A_53]: (k1_relat_1('#skF_7'(A_53))=A_53 | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.48/4.36  tff(c_46, plain, (![A_53]: (v1_relat_1('#skF_7'(A_53)) | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.48/4.36  tff(c_12526, plain, (![A_497, C_498]: (r2_hidden('#skF_5'('#skF_7'(A_497), k2_relat_1('#skF_7'(A_497)), C_498), A_497) | ~r2_hidden(C_498, k2_relat_1('#skF_7'(A_497))) | ~v1_funct_1('#skF_7'(A_497)) | ~v1_relat_1('#skF_7'(A_497)) | k1_xboole_0=A_497)), inference(superposition, [status(thm), theory('equality')], [c_38, c_248])).
% 12.48/4.36  tff(c_12547, plain, (![C_498]: (~r2_hidden(C_498, k2_relat_1('#skF_7'('#skF_10'))) | ~v1_funct_1('#skF_7'('#skF_10')) | ~v1_relat_1('#skF_7'('#skF_10')) | k1_xboole_0='#skF_10')), inference(resolution, [status(thm)], [c_12526, c_7568])).
% 12.48/4.36  tff(c_12600, plain, (![C_498]: (~r2_hidden(C_498, k2_relat_1('#skF_7'('#skF_10'))) | ~v1_funct_1('#skF_7'('#skF_10')) | ~v1_relat_1('#skF_7'('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_55, c_12547])).
% 12.48/4.36  tff(c_14889, plain, (~v1_relat_1('#skF_7'('#skF_10'))), inference(splitLeft, [status(thm)], [c_12600])).
% 12.48/4.36  tff(c_14892, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_46, c_14889])).
% 12.48/4.36  tff(c_14896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_14892])).
% 12.48/4.36  tff(c_14898, plain, (v1_relat_1('#skF_7'('#skF_10'))), inference(splitRight, [status(thm)], [c_12600])).
% 12.48/4.36  tff(c_44, plain, (![A_53]: (v1_funct_1('#skF_7'(A_53)) | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.48/4.36  tff(c_14897, plain, (![C_498]: (~v1_funct_1('#skF_7'('#skF_10')) | ~r2_hidden(C_498, k2_relat_1('#skF_7'('#skF_10'))))), inference(splitRight, [status(thm)], [c_12600])).
% 12.48/4.36  tff(c_14903, plain, (~v1_funct_1('#skF_7'('#skF_10'))), inference(splitLeft, [status(thm)], [c_14897])).
% 12.48/4.36  tff(c_14906, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_44, c_14903])).
% 12.48/4.36  tff(c_14910, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_14906])).
% 12.48/4.36  tff(c_14912, plain, (v1_funct_1('#skF_7'('#skF_10'))), inference(splitRight, [status(thm)], [c_14897])).
% 12.48/4.36  tff(c_15090, plain, (![C_520]: (~r2_hidden(C_520, k2_relat_1('#skF_7'('#skF_10'))))), inference(splitRight, [status(thm)], [c_14897])).
% 12.48/4.36  tff(c_15497, plain, (![C_526, B_527]: (~r2_hidden(C_526, k2_relat_1('#skF_6'(k2_relat_1('#skF_7'('#skF_10')), B_527))))), inference(resolution, [status(thm)], [c_271, c_15090])).
% 12.48/4.36  tff(c_15585, plain, (![B_237]: ('#skF_6'(k1_relat_1('#skF_7'('#skF_10')), B_237)='#skF_7'('#skF_10') | ~v1_funct_1('#skF_7'('#skF_10')) | ~v1_relat_1('#skF_7'('#skF_10')))), inference(resolution, [status(thm)], [c_2397, c_15497])).
% 12.48/4.36  tff(c_15707, plain, (![B_528]: ('#skF_6'(k1_relat_1('#skF_7'('#skF_10')), B_528)='#skF_7'('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_14898, c_14912, c_15585])).
% 12.48/4.36  tff(c_15979, plain, (![B_528]: ('#skF_7'('#skF_10')='#skF_6'('#skF_10', B_528) | k1_xboole_0='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_38, c_15707])).
% 12.48/4.36  tff(c_16132, plain, ('#skF_7'('#skF_10')='#skF_8'('#skF_10') | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_14219, c_15979])).
% 12.48/4.36  tff(c_16133, plain, ('#skF_7'('#skF_10')='#skF_8'('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_55, c_16132])).
% 12.48/4.36  tff(c_34, plain, (![A_53]: ('#skF_7'(A_53)!='#skF_8'(A_53) | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.48/4.36  tff(c_16167, plain, (k1_xboole_0='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_16133, c_34])).
% 12.48/4.36  tff(c_16194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_16167])).
% 12.48/4.36  tff(c_16196, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_54])).
% 12.48/4.36  tff(c_16195, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_54])).
% 12.48/4.36  tff(c_16201, plain, ('#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_16196, c_16195])).
% 12.48/4.36  tff(c_16211, plain, (![C_65]: (~r1_tarski(k2_relat_1(C_65), '#skF_10') | k1_relat_1(C_65)!='#skF_10' | ~v1_funct_1(C_65) | ~v1_relat_1(C_65))), inference(demodulation, [status(thm), theory('equality')], [c_16201, c_52])).
% 12.48/4.36  tff(c_16547, plain, (![A_604, B_605, B_603]: (k1_relat_1('#skF_6'(A_604, B_605))!='#skF_10' | ~v1_funct_1('#skF_6'(A_604, B_605)) | ~v1_relat_1('#skF_6'(A_604, B_605)) | r2_hidden(B_603, k2_relat_1('#skF_6'(A_604, B_603))))), inference(resolution, [status(thm)], [c_16529, c_16211])).
% 12.48/4.36  tff(c_16559, plain, (![A_604, B_603]: (A_604!='#skF_10' | r2_hidden(B_603, k2_relat_1('#skF_6'(A_604, B_603))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_16547])).
% 12.48/4.36  tff(c_16332, plain, (![A_46, B_47, C_570]: (r2_hidden('#skF_5'('#skF_6'(A_46, B_47), k2_relat_1('#skF_6'(A_46, B_47)), C_570), A_46) | ~r2_hidden(C_570, k2_relat_1('#skF_6'(A_46, B_47))) | ~v1_funct_1('#skF_6'(A_46, B_47)) | ~v1_relat_1('#skF_6'(A_46, B_47)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_16319])).
% 12.48/4.36  tff(c_16336, plain, (![A_46, B_47, C_570]: (r2_hidden('#skF_5'('#skF_6'(A_46, B_47), k2_relat_1('#skF_6'(A_46, B_47)), C_570), A_46) | ~r2_hidden(C_570, k2_relat_1('#skF_6'(A_46, B_47))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_16332])).
% 12.48/4.36  tff(c_16256, plain, (![A_545, B_546]: (~r2_hidden('#skF_1'(A_545, B_546), B_546) | r1_tarski(A_545, B_546))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.48/4.36  tff(c_16261, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_16256])).
% 12.48/4.36  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.48/4.36  tff(c_16334, plain, (![A_569, C_570, B_2]: (r2_hidden('#skF_5'(A_569, k2_relat_1(A_569), C_570), B_2) | ~r1_tarski(k1_relat_1(A_569), B_2) | ~r2_hidden(C_570, k2_relat_1(A_569)) | ~v1_funct_1(A_569) | ~v1_relat_1(A_569))), inference(resolution, [status(thm)], [c_16319, c_2])).
% 12.48/4.36  tff(c_16410, plain, (![A_590, C_591]: (k1_funct_1(A_590, '#skF_5'(A_590, k2_relat_1(A_590), C_591))=C_591 | ~r2_hidden(C_591, k2_relat_1(A_590)) | ~v1_funct_1(A_590) | ~v1_relat_1(A_590))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.48/4.36  tff(c_16420, plain, (![C_591, B_47, A_46]: (C_591=B_47 | ~r2_hidden('#skF_5'('#skF_6'(A_46, B_47), k2_relat_1('#skF_6'(A_46, B_47)), C_591), A_46) | ~r2_hidden(C_591, k2_relat_1('#skF_6'(A_46, B_47))) | ~v1_funct_1('#skF_6'(A_46, B_47)) | ~v1_relat_1('#skF_6'(A_46, B_47)))), inference(superposition, [status(thm), theory('equality')], [c_16410, c_26])).
% 12.48/4.36  tff(c_23177, plain, (![C_881, B_882, A_883]: (C_881=B_882 | ~r2_hidden('#skF_5'('#skF_6'(A_883, B_882), k2_relat_1('#skF_6'(A_883, B_882)), C_881), A_883) | ~r2_hidden(C_881, k2_relat_1('#skF_6'(A_883, B_882))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_16420])).
% 12.48/4.36  tff(c_23181, plain, (![C_570, B_882, B_2]: (C_570=B_882 | ~r1_tarski(k1_relat_1('#skF_6'(B_2, B_882)), B_2) | ~r2_hidden(C_570, k2_relat_1('#skF_6'(B_2, B_882))) | ~v1_funct_1('#skF_6'(B_2, B_882)) | ~v1_relat_1('#skF_6'(B_2, B_882)))), inference(resolution, [status(thm)], [c_16334, c_23177])).
% 12.48/4.36  tff(c_23249, plain, (![C_884, B_885, B_886]: (C_884=B_885 | ~r2_hidden(C_884, k2_relat_1('#skF_6'(B_886, B_885))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_16261, c_28, c_23181])).
% 12.48/4.36  tff(c_23706, plain, (![B_895, B_896, B_897]: ('#skF_1'(k2_relat_1('#skF_6'(B_895, B_896)), B_897)=B_896 | r1_tarski(k2_relat_1('#skF_6'(B_895, B_896)), B_897))), inference(resolution, [status(thm)], [c_6, c_23249])).
% 12.48/4.36  tff(c_23773, plain, (![B_895, B_896]: (k1_relat_1('#skF_6'(B_895, B_896))!='#skF_10' | ~v1_funct_1('#skF_6'(B_895, B_896)) | ~v1_relat_1('#skF_6'(B_895, B_896)) | '#skF_1'(k2_relat_1('#skF_6'(B_895, B_896)), '#skF_10')=B_896)), inference(resolution, [status(thm)], [c_23706, c_16211])).
% 12.48/4.36  tff(c_23833, plain, (![B_898, B_899]: (B_898!='#skF_10' | '#skF_1'(k2_relat_1('#skF_6'(B_898, B_899)), '#skF_10')=B_899)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_23773])).
% 12.48/4.36  tff(c_23882, plain, (![B_900, B_901]: (~r2_hidden(B_900, '#skF_10') | r1_tarski(k2_relat_1('#skF_6'(B_901, B_900)), '#skF_10') | B_901!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_23833, c_4])).
% 12.48/4.36  tff(c_23933, plain, (![B_901, B_900]: (k1_relat_1('#skF_6'(B_901, B_900))!='#skF_10' | ~v1_funct_1('#skF_6'(B_901, B_900)) | ~v1_relat_1('#skF_6'(B_901, B_900)) | ~r2_hidden(B_900, '#skF_10') | B_901!='#skF_10')), inference(resolution, [status(thm)], [c_23882, c_16211])).
% 12.48/4.36  tff(c_23989, plain, (![B_900, B_901]: (~r2_hidden(B_900, '#skF_10') | B_901!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_23933])).
% 12.48/4.36  tff(c_23990, plain, (![B_901]: (B_901!='#skF_10')), inference(splitLeft, [status(thm)], [c_23989])).
% 12.48/4.36  tff(c_24002, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23990, c_16201])).
% 12.48/4.36  tff(c_24179, plain, (![B_905]: (~r2_hidden(B_905, '#skF_10'))), inference(splitRight, [status(thm)], [c_23989])).
% 12.48/4.36  tff(c_24264, plain, (![C_907, B_908]: (~r2_hidden(C_907, k2_relat_1('#skF_6'('#skF_10', B_908))))), inference(resolution, [status(thm)], [c_16336, c_24179])).
% 12.48/4.36  tff(c_24392, plain, $false, inference(resolution, [status(thm)], [c_16559, c_24264])).
% 12.48/4.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.48/4.36  
% 12.48/4.36  Inference rules
% 12.48/4.36  ----------------------
% 12.48/4.36  #Ref     : 6
% 12.48/4.36  #Sup     : 6507
% 12.48/4.36  #Fact    : 0
% 12.48/4.36  #Define  : 0
% 12.48/4.36  #Split   : 11
% 12.48/4.36  #Chain   : 0
% 12.48/4.36  #Close   : 0
% 12.48/4.36  
% 12.48/4.36  Ordering : KBO
% 12.48/4.36  
% 12.48/4.36  Simplification rules
% 12.48/4.36  ----------------------
% 12.48/4.36  #Subsume      : 3616
% 12.48/4.36  #Demod        : 2029
% 12.48/4.36  #Tautology    : 574
% 12.48/4.36  #SimpNegUnit  : 401
% 12.48/4.36  #BackRed      : 33
% 12.48/4.36  
% 12.48/4.36  #Partial instantiations: 0
% 12.48/4.36  #Strategies tried      : 1
% 12.48/4.36  
% 12.48/4.36  Timing (in seconds)
% 12.48/4.36  ----------------------
% 12.48/4.36  Preprocessing        : 0.31
% 12.48/4.36  Parsing              : 0.15
% 12.48/4.36  CNF conversion       : 0.03
% 12.48/4.36  Main loop            : 3.21
% 12.48/4.36  Inferencing          : 0.90
% 12.48/4.36  Reduction            : 0.89
% 12.48/4.36  Demodulation         : 0.65
% 12.48/4.36  BG Simplification    : 0.09
% 12.48/4.36  Subsumption          : 1.12
% 12.48/4.36  Abstraction          : 0.16
% 12.48/4.36  MUC search           : 0.00
% 12.48/4.36  Cooper               : 0.00
% 12.48/4.36  Total                : 3.58
% 12.48/4.36  Index Insertion      : 0.00
% 12.48/4.36  Index Deletion       : 0.00
% 12.48/4.36  Index Matching       : 0.00
% 12.48/4.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
