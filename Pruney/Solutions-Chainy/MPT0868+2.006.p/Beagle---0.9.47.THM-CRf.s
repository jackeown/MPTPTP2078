%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:24 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 271 expanded)
%              Number of leaves         :   26 (  99 expanded)
%              Depth                    :    9
%              Number of atoms          :  136 ( 642 expanded)
%              Number of equality atoms :   73 ( 256 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => ( C != k1_mcart_1(C)
                  & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_422,plain,(
    ! [B_85,A_86] :
      ( v1_xboole_0(B_85)
      | ~ m1_subset_1(B_85,A_86)
      | ~ v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_430,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_422])).

tff(c_431,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_430])).

tff(c_28,plain,(
    ! [A_16,B_17] : k2_mcart_1(k4_tarski(A_16,B_17)) = B_17 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,(
    ! [B_12,C_13] : k2_mcart_1(k4_tarski(B_12,C_13)) != k4_tarski(B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,(
    ! [B_12,C_13] : k4_tarski(B_12,C_13) != C_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_20])).

tff(c_14,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_95,plain,(
    ! [B_35,A_36] :
      ( v1_xboole_0(B_35)
      | ~ m1_subset_1(B_35,A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_103,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_95])).

tff(c_104,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_26,plain,(
    ! [A_16,B_17] : k1_mcart_1(k4_tarski(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    ! [B_12,C_13] : k1_mcart_1(k4_tarski(B_12,C_13)) != k4_tarski(B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_37,plain,(
    ! [B_12,C_13] : k4_tarski(B_12,C_13) != B_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22])).

tff(c_30,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_61,plain,(
    k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( r2_hidden(B_3,A_2)
      | ~ m1_subset_1(B_3,A_2)
      | v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_225,plain,(
    ! [A_63,B_64] :
      ( k4_tarski(k1_mcart_1(A_63),k2_mcart_1(A_63)) = A_63
      | ~ r2_hidden(A_63,B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_230,plain,(
    ! [B_67,A_68] :
      ( k4_tarski(k1_mcart_1(B_67),k2_mcart_1(B_67)) = B_67
      | ~ v1_relat_1(A_68)
      | ~ m1_subset_1(B_67,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_6,c_225])).

tff(c_234,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_230])).

tff(c_238,plain,
    ( k4_tarski('#skF_3',k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_61,c_234])).

tff(c_240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_37,c_238])).

tff(c_241,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_250,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_241,c_2])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_255,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_36])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_254,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_34])).

tff(c_66,plain,(
    ! [A_30] :
      ( v1_xboole_0(k2_relat_1(A_30))
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_70,plain,(
    ! [A_30] :
      ( k2_relat_1(A_30) = k1_xboole_0
      | ~ v1_xboole_0(A_30) ) ),
    inference(resolution,[status(thm)],[c_66,c_2])).

tff(c_249,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_241,c_70])).

tff(c_261,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_249])).

tff(c_242,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_276,plain,(
    ! [A_73] :
      ( A_73 = '#skF_3'
      | ~ v1_xboole_0(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_2])).

tff(c_286,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_242,c_276])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( k2_relat_1(k2_zfmisc_1(A_7,B_8)) = B_8
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_366,plain,(
    ! [A_78,B_79] :
      ( k2_relat_1(k2_zfmisc_1(A_78,B_79)) = B_79
      | B_79 = '#skF_3'
      | A_78 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_250,c_16])).

tff(c_381,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_366])).

tff(c_384,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_381])).

tff(c_386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_254,c_254,c_384])).

tff(c_387,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_551,plain,(
    ! [A_111,B_112] :
      ( k4_tarski(k1_mcart_1(A_111),k2_mcart_1(A_111)) = A_111
      | ~ r2_hidden(A_111,B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_556,plain,(
    ! [B_115,A_116] :
      ( k4_tarski(k1_mcart_1(B_115),k2_mcart_1(B_115)) = B_115
      | ~ v1_relat_1(A_116)
      | ~ m1_subset_1(B_115,A_116)
      | v1_xboole_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_6,c_551])).

tff(c_560,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_556])).

tff(c_564,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),'#skF_3') = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_387,c_560])).

tff(c_566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_431,c_38,c_564])).

tff(c_567,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_430])).

tff(c_576,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_567,c_2])).

tff(c_581,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_36])).

tff(c_580,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_34])).

tff(c_393,plain,(
    ! [A_80] :
      ( v1_xboole_0(k2_relat_1(A_80))
      | ~ v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_397,plain,(
    ! [A_80] :
      ( k2_relat_1(A_80) = k1_xboole_0
      | ~ v1_xboole_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_393,c_2])).

tff(c_575,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_567,c_397])).

tff(c_587,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_575])).

tff(c_568,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_430])).

tff(c_602,plain,(
    ! [A_121] :
      ( A_121 = '#skF_3'
      | ~ v1_xboole_0(A_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_2])).

tff(c_612,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_568,c_602])).

tff(c_692,plain,(
    ! [A_126,B_127] :
      ( k2_relat_1(k2_zfmisc_1(A_126,B_127)) = B_127
      | B_127 = '#skF_3'
      | A_126 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_576,c_16])).

tff(c_707,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_692])).

tff(c_710,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_707])).

tff(c_712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_581,c_580,c_580,c_710])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.41  
% 2.69/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.41  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.69/1.41  
% 2.69/1.41  %Foreground sorts:
% 2.69/1.41  
% 2.69/1.41  
% 2.69/1.41  %Background operators:
% 2.69/1.41  
% 2.69/1.41  
% 2.69/1.41  %Foreground operators:
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.69/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.69/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.41  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.69/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.41  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.69/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.69/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.69/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.41  
% 2.69/1.43  tff(f_97, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_mcart_1)).
% 2.69/1.43  tff(f_42, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.69/1.43  tff(f_79, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.69/1.43  tff(f_69, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.69/1.43  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.69/1.43  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 2.69/1.43  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.69/1.43  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 2.69/1.43  tff(f_60, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 2.69/1.43  tff(c_32, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.69/1.43  tff(c_422, plain, (![B_85, A_86]: (v1_xboole_0(B_85) | ~m1_subset_1(B_85, A_86) | ~v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.69/1.43  tff(c_430, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_422])).
% 2.69/1.43  tff(c_431, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_430])).
% 2.69/1.43  tff(c_28, plain, (![A_16, B_17]: (k2_mcart_1(k4_tarski(A_16, B_17))=B_17)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.69/1.43  tff(c_20, plain, (![B_12, C_13]: (k2_mcart_1(k4_tarski(B_12, C_13))!=k4_tarski(B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.69/1.43  tff(c_38, plain, (![B_12, C_13]: (k4_tarski(B_12, C_13)!=C_13)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_20])).
% 2.69/1.43  tff(c_14, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.69/1.43  tff(c_95, plain, (![B_35, A_36]: (v1_xboole_0(B_35) | ~m1_subset_1(B_35, A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.69/1.43  tff(c_103, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_95])).
% 2.69/1.43  tff(c_104, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_103])).
% 2.69/1.43  tff(c_26, plain, (![A_16, B_17]: (k1_mcart_1(k4_tarski(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.69/1.43  tff(c_22, plain, (![B_12, C_13]: (k1_mcart_1(k4_tarski(B_12, C_13))!=k4_tarski(B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.69/1.43  tff(c_37, plain, (![B_12, C_13]: (k4_tarski(B_12, C_13)!=B_12)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22])).
% 2.69/1.43  tff(c_30, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.69/1.43  tff(c_61, plain, (k1_mcart_1('#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_30])).
% 2.69/1.43  tff(c_6, plain, (![B_3, A_2]: (r2_hidden(B_3, A_2) | ~m1_subset_1(B_3, A_2) | v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.69/1.43  tff(c_225, plain, (![A_63, B_64]: (k4_tarski(k1_mcart_1(A_63), k2_mcart_1(A_63))=A_63 | ~r2_hidden(A_63, B_64) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.69/1.43  tff(c_230, plain, (![B_67, A_68]: (k4_tarski(k1_mcart_1(B_67), k2_mcart_1(B_67))=B_67 | ~v1_relat_1(A_68) | ~m1_subset_1(B_67, A_68) | v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_6, c_225])).
% 2.69/1.43  tff(c_234, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_230])).
% 2.69/1.43  tff(c_238, plain, (k4_tarski('#skF_3', k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_61, c_234])).
% 2.69/1.43  tff(c_240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_37, c_238])).
% 2.69/1.43  tff(c_241, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_103])).
% 2.69/1.43  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.43  tff(c_250, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_241, c_2])).
% 2.69/1.43  tff(c_36, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.69/1.43  tff(c_255, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_250, c_36])).
% 2.69/1.43  tff(c_34, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.69/1.43  tff(c_254, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_250, c_34])).
% 2.69/1.43  tff(c_66, plain, (![A_30]: (v1_xboole_0(k2_relat_1(A_30)) | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.69/1.43  tff(c_70, plain, (![A_30]: (k2_relat_1(A_30)=k1_xboole_0 | ~v1_xboole_0(A_30))), inference(resolution, [status(thm)], [c_66, c_2])).
% 2.69/1.43  tff(c_249, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_241, c_70])).
% 2.69/1.43  tff(c_261, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_250, c_249])).
% 2.69/1.43  tff(c_242, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_103])).
% 2.69/1.43  tff(c_276, plain, (![A_73]: (A_73='#skF_3' | ~v1_xboole_0(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_2])).
% 2.69/1.43  tff(c_286, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_242, c_276])).
% 2.69/1.43  tff(c_16, plain, (![A_7, B_8]: (k2_relat_1(k2_zfmisc_1(A_7, B_8))=B_8 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.69/1.43  tff(c_366, plain, (![A_78, B_79]: (k2_relat_1(k2_zfmisc_1(A_78, B_79))=B_79 | B_79='#skF_3' | A_78='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_250, c_250, c_16])).
% 2.69/1.43  tff(c_381, plain, (k2_relat_1('#skF_3')='#skF_2' | '#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_286, c_366])).
% 2.69/1.43  tff(c_384, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_261, c_381])).
% 2.69/1.43  tff(c_386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_255, c_254, c_254, c_384])).
% 2.69/1.43  tff(c_387, plain, (k2_mcart_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 2.69/1.43  tff(c_551, plain, (![A_111, B_112]: (k4_tarski(k1_mcart_1(A_111), k2_mcart_1(A_111))=A_111 | ~r2_hidden(A_111, B_112) | ~v1_relat_1(B_112))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.69/1.43  tff(c_556, plain, (![B_115, A_116]: (k4_tarski(k1_mcart_1(B_115), k2_mcart_1(B_115))=B_115 | ~v1_relat_1(A_116) | ~m1_subset_1(B_115, A_116) | v1_xboole_0(A_116))), inference(resolution, [status(thm)], [c_6, c_551])).
% 2.69/1.43  tff(c_560, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_556])).
% 2.69/1.43  tff(c_564, plain, (k4_tarski(k1_mcart_1('#skF_3'), '#skF_3')='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_387, c_560])).
% 2.69/1.43  tff(c_566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_431, c_38, c_564])).
% 2.69/1.43  tff(c_567, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_430])).
% 2.69/1.43  tff(c_576, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_567, c_2])).
% 2.69/1.43  tff(c_581, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_576, c_36])).
% 2.69/1.43  tff(c_580, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_576, c_34])).
% 2.69/1.43  tff(c_393, plain, (![A_80]: (v1_xboole_0(k2_relat_1(A_80)) | ~v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.69/1.43  tff(c_397, plain, (![A_80]: (k2_relat_1(A_80)=k1_xboole_0 | ~v1_xboole_0(A_80))), inference(resolution, [status(thm)], [c_393, c_2])).
% 2.69/1.43  tff(c_575, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_567, c_397])).
% 2.69/1.43  tff(c_587, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_576, c_575])).
% 2.69/1.43  tff(c_568, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_430])).
% 2.69/1.43  tff(c_602, plain, (![A_121]: (A_121='#skF_3' | ~v1_xboole_0(A_121))), inference(demodulation, [status(thm), theory('equality')], [c_576, c_2])).
% 2.69/1.43  tff(c_612, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_568, c_602])).
% 2.69/1.43  tff(c_692, plain, (![A_126, B_127]: (k2_relat_1(k2_zfmisc_1(A_126, B_127))=B_127 | B_127='#skF_3' | A_126='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_576, c_576, c_16])).
% 2.69/1.43  tff(c_707, plain, (k2_relat_1('#skF_3')='#skF_2' | '#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_612, c_692])).
% 2.69/1.43  tff(c_710, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_587, c_707])).
% 2.69/1.43  tff(c_712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_581, c_580, c_580, c_710])).
% 2.69/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.43  
% 2.69/1.43  Inference rules
% 2.69/1.43  ----------------------
% 2.69/1.43  #Ref     : 0
% 2.69/1.43  #Sup     : 142
% 2.69/1.43  #Fact    : 0
% 2.69/1.43  #Define  : 0
% 2.69/1.43  #Split   : 5
% 2.69/1.43  #Chain   : 0
% 2.69/1.43  #Close   : 0
% 2.69/1.43  
% 2.69/1.43  Ordering : KBO
% 2.69/1.43  
% 2.69/1.43  Simplification rules
% 2.69/1.43  ----------------------
% 2.69/1.43  #Subsume      : 24
% 2.69/1.43  #Demod        : 70
% 2.69/1.43  #Tautology    : 98
% 2.69/1.43  #SimpNegUnit  : 16
% 2.69/1.43  #BackRed      : 16
% 2.69/1.43  
% 2.69/1.43  #Partial instantiations: 0
% 2.69/1.43  #Strategies tried      : 1
% 2.69/1.43  
% 2.69/1.43  Timing (in seconds)
% 2.69/1.43  ----------------------
% 2.69/1.43  Preprocessing        : 0.31
% 2.69/1.43  Parsing              : 0.17
% 2.69/1.43  CNF conversion       : 0.02
% 2.69/1.43  Main loop            : 0.30
% 2.69/1.43  Inferencing          : 0.12
% 2.69/1.43  Reduction            : 0.08
% 2.69/1.43  Demodulation         : 0.05
% 2.69/1.43  BG Simplification    : 0.02
% 2.69/1.43  Subsumption          : 0.06
% 2.69/1.43  Abstraction          : 0.01
% 2.69/1.43  MUC search           : 0.00
% 2.69/1.43  Cooper               : 0.00
% 2.69/1.43  Total                : 0.65
% 2.69/1.43  Index Insertion      : 0.00
% 2.69/1.43  Index Deletion       : 0.00
% 2.69/1.43  Index Matching       : 0.00
% 2.69/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
