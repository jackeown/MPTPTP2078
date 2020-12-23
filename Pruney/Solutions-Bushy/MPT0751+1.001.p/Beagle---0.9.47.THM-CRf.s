%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0751+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:48 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 100 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  162 ( 287 expanded)
%              Number of equality atoms :   19 (  41 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v4_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_xboole_0 > v1_ordinal1 > #nlpp > k1_ordinal1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(v4_ordinal1,type,(
    v4_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ( ~ ( ~ v4_ordinal1(A)
              & ! [B] :
                  ( v3_ordinal1(B)
                 => A != k1_ordinal1(B) ) )
          & ~ ( ? [B] :
                  ( v3_ordinal1(B)
                  & A = k1_ordinal1(B) )
              & v4_ordinal1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_ordinal1)).

tff(f_88,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v4_ordinal1(A)
      <=> ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(B,A)
             => r2_hidden(k1_ordinal1(B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

tff(f_49,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( ~ v1_xboole_0(k1_ordinal1(A))
        & v3_ordinal1(k1_ordinal1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_ordinal1)).

tff(f_35,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_77,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
          <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_59,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_38,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_36,plain,(
    ! [A_16] :
      ( v3_ordinal1('#skF_1'(A_16))
      | v4_ordinal1(A_16)
      | ~ v3_ordinal1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_34,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_1'(A_16),A_16)
      | v4_ordinal1(A_16)
      | ~ v3_ordinal1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_65,plain,(
    ! [A_28] :
      ( v3_ordinal1(k1_ordinal1(A_28))
      | ~ v3_ordinal1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_ordinal1(A_3)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    ! [A_28] :
      ( v1_ordinal1(k1_ordinal1(A_28))
      | ~ v3_ordinal1(A_28) ) ),
    inference(resolution,[status(thm)],[c_65,c_6])).

tff(c_14,plain,(
    ! [A_6] :
      ( v3_ordinal1(k1_ordinal1(A_6))
      | ~ v3_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    ! [A_13,B_15] :
      ( r1_ordinal1(k1_ordinal1(A_13),B_15)
      | ~ r2_hidden(A_13,B_15)
      | ~ v3_ordinal1(B_15)
      | ~ v3_ordinal1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ r1_ordinal1(A_7,B_8)
      | ~ v3_ordinal1(B_8)
      | ~ v3_ordinal1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r2_xboole_0(A_4,B_5)
      | B_5 = A_4
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_133,plain,(
    ! [A_51,B_52] :
      ( r2_hidden(A_51,B_52)
      | ~ r2_xboole_0(A_51,B_52)
      | ~ v3_ordinal1(B_52)
      | ~ v1_ordinal1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_144,plain,(
    ! [A_57,B_58] :
      ( r2_hidden(A_57,B_58)
      | ~ v3_ordinal1(B_58)
      | ~ v1_ordinal1(A_57)
      | B_58 = A_57
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_8,c_133])).

tff(c_32,plain,(
    ! [A_16] :
      ( ~ r2_hidden(k1_ordinal1('#skF_1'(A_16)),A_16)
      | v4_ordinal1(A_16)
      | ~ v3_ordinal1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_293,plain,(
    ! [B_80] :
      ( v4_ordinal1(B_80)
      | ~ v3_ordinal1(B_80)
      | ~ v1_ordinal1(k1_ordinal1('#skF_1'(B_80)))
      | k1_ordinal1('#skF_1'(B_80)) = B_80
      | ~ r1_tarski(k1_ordinal1('#skF_1'(B_80)),B_80) ) ),
    inference(resolution,[status(thm)],[c_144,c_32])).

tff(c_316,plain,(
    ! [B_84] :
      ( v4_ordinal1(B_84)
      | ~ v1_ordinal1(k1_ordinal1('#skF_1'(B_84)))
      | k1_ordinal1('#skF_1'(B_84)) = B_84
      | ~ r1_ordinal1(k1_ordinal1('#skF_1'(B_84)),B_84)
      | ~ v3_ordinal1(B_84)
      | ~ v3_ordinal1(k1_ordinal1('#skF_1'(B_84))) ) ),
    inference(resolution,[status(thm)],[c_20,c_293])).

tff(c_334,plain,(
    ! [B_89] :
      ( v4_ordinal1(B_89)
      | ~ v1_ordinal1(k1_ordinal1('#skF_1'(B_89)))
      | k1_ordinal1('#skF_1'(B_89)) = B_89
      | ~ v3_ordinal1(k1_ordinal1('#skF_1'(B_89)))
      | ~ r2_hidden('#skF_1'(B_89),B_89)
      | ~ v3_ordinal1(B_89)
      | ~ v3_ordinal1('#skF_1'(B_89)) ) ),
    inference(resolution,[status(thm)],[c_28,c_316])).

tff(c_339,plain,(
    ! [B_90] :
      ( v4_ordinal1(B_90)
      | ~ v1_ordinal1(k1_ordinal1('#skF_1'(B_90)))
      | k1_ordinal1('#skF_1'(B_90)) = B_90
      | ~ r2_hidden('#skF_1'(B_90),B_90)
      | ~ v3_ordinal1(B_90)
      | ~ v3_ordinal1('#skF_1'(B_90)) ) ),
    inference(resolution,[status(thm)],[c_14,c_334])).

tff(c_344,plain,(
    ! [B_91] :
      ( v4_ordinal1(B_91)
      | k1_ordinal1('#skF_1'(B_91)) = B_91
      | ~ r2_hidden('#skF_1'(B_91),B_91)
      | ~ v3_ordinal1(B_91)
      | ~ v3_ordinal1('#skF_1'(B_91)) ) ),
    inference(resolution,[status(thm)],[c_73,c_339])).

tff(c_354,plain,(
    ! [A_92] :
      ( k1_ordinal1('#skF_1'(A_92)) = A_92
      | ~ v3_ordinal1('#skF_1'(A_92))
      | v4_ordinal1(A_92)
      | ~ v3_ordinal1(A_92) ) ),
    inference(resolution,[status(thm)],[c_34,c_344])).

tff(c_365,plain,(
    ! [A_94] :
      ( k1_ordinal1('#skF_1'(A_94)) = A_94
      | v4_ordinal1(A_94)
      | ~ v3_ordinal1(A_94) ) ),
    inference(resolution,[status(thm)],[c_36,c_354])).

tff(c_50,plain,
    ( ~ v4_ordinal1('#skF_2')
    | v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_62,plain,(
    ~ v4_ordinal1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_40,plain,(
    ! [B_22] :
      ( k1_ordinal1(B_22) != '#skF_2'
      | ~ v3_ordinal1(B_22)
      | v4_ordinal1('#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_93,plain,(
    ! [B_37] :
      ( k1_ordinal1(B_37) != '#skF_2'
      | ~ v3_ordinal1(B_37) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_40])).

tff(c_103,plain,(
    ! [A_16] :
      ( k1_ordinal1('#skF_1'(A_16)) != '#skF_2'
      | v4_ordinal1(A_16)
      | ~ v3_ordinal1(A_16) ) ),
    inference(resolution,[status(thm)],[c_36,c_93])).

tff(c_410,plain,(
    ! [A_94] :
      ( A_94 != '#skF_2'
      | v4_ordinal1(A_94)
      | ~ v3_ordinal1(A_94)
      | v4_ordinal1(A_94)
      | ~ v3_ordinal1(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_103])).

tff(c_470,plain,(
    ! [A_98] :
      ( A_98 != '#skF_2'
      | ~ v3_ordinal1(A_98)
      | v4_ordinal1(A_98) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_410])).

tff(c_476,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_470,c_62])).

tff(c_481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_476])).

tff(c_483,plain,(
    v4_ordinal1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_46,plain,
    ( ~ v4_ordinal1('#skF_2')
    | k1_ordinal1('#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_503,plain,(
    k1_ordinal1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_46])).

tff(c_22,plain,(
    ! [A_9] : r2_hidden(A_9,k1_ordinal1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_510,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_22])).

tff(c_482,plain,(
    v3_ordinal1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_696,plain,(
    ! [B_132,A_133] :
      ( r2_hidden(k1_ordinal1(B_132),A_133)
      | ~ r2_hidden(B_132,A_133)
      | ~ v3_ordinal1(B_132)
      | ~ v4_ordinal1(A_133)
      | ~ v3_ordinal1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_717,plain,(
    ! [A_133] :
      ( r2_hidden('#skF_2',A_133)
      | ~ r2_hidden('#skF_3',A_133)
      | ~ v3_ordinal1('#skF_3')
      | ~ v4_ordinal1(A_133)
      | ~ v3_ordinal1(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_696])).

tff(c_755,plain,(
    ! [A_135] :
      ( r2_hidden('#skF_2',A_135)
      | ~ r2_hidden('#skF_3',A_135)
      | ~ v4_ordinal1(A_135)
      | ~ v3_ordinal1(A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_717])).

tff(c_534,plain,(
    ! [B_104,A_105] :
      ( ~ r2_hidden(B_104,A_105)
      | ~ r2_hidden(A_105,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_540,plain,(
    ! [A_9] : ~ r2_hidden(k1_ordinal1(A_9),A_9) ),
    inference(resolution,[status(thm)],[c_22,c_534])).

tff(c_723,plain,(
    ! [A_133] :
      ( ~ r2_hidden(A_133,A_133)
      | ~ v4_ordinal1(A_133)
      | ~ v3_ordinal1(A_133) ) ),
    inference(resolution,[status(thm)],[c_696,c_540])).

tff(c_759,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ v4_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_755,c_723])).

tff(c_776,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_483,c_510,c_759])).

%------------------------------------------------------------------------------
