%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:42 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 167 expanded)
%              Number of leaves         :   37 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :  173 ( 476 expanded)
%              Number of equality atoms :   21 (  76 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v2_relat_1,type,(
    v2_relat_1: $i > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v5_funct_1(A,B)
                & k1_relat_1(A) = k1_relat_1(B) )
             => v2_relat_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_relat_1(A)
      <=> ! [B] :
            ~ ( r2_hidden(B,k1_relat_1(A))
              & v1_xboole_0(k1_funct_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_51,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_48,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_79,axiom,(
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

tff(c_40,plain,(
    ~ v2_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_48,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_44,plain,(
    v5_funct_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_26,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_1'(A_13),k1_relat_1(A_13))
      | v2_relat_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_52,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_42,plain,(
    k1_relat_1('#skF_3') = k1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_74,plain,(
    ! [A_37] :
      ( k7_relat_1(A_37,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_82,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_74])).

tff(c_91,plain,(
    ! [A_38,B_39] :
      ( v1_relat_1(k7_relat_1(A_38,B_39))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_97,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_91])).

tff(c_103,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_97])).

tff(c_129,plain,(
    ! [A_41,B_42] :
      ( v1_funct_1(k7_relat_1(A_41,B_42))
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_135,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_129])).

tff(c_142,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_135])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_12] : k9_relat_1(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_365,plain,(
    ! [C_73,A_74,B_75] :
      ( k2_tarski(k1_funct_1(C_73,A_74),k1_funct_1(C_73,B_75)) = k9_relat_1(C_73,k2_tarski(A_74,B_75))
      | ~ r2_hidden(B_75,k1_relat_1(C_73))
      | ~ r2_hidden(A_74,k1_relat_1(C_73))
      | ~ v1_funct_1(C_73)
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_146,plain,(
    ! [A_43,B_44] : k2_xboole_0(k1_tarski(A_43),k1_tarski(B_44)) = k2_tarski(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7,B_8] : k2_xboole_0(k1_tarski(A_7),B_8) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_151,plain,(
    ! [A_43,B_44] : k2_tarski(A_43,B_44) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_10])).

tff(c_382,plain,(
    ! [C_76,A_77,B_78] :
      ( k9_relat_1(C_76,k2_tarski(A_77,B_78)) != k1_xboole_0
      | ~ r2_hidden(B_78,k1_relat_1(C_76))
      | ~ r2_hidden(A_77,k1_relat_1(C_76))
      | ~ v1_funct_1(C_76)
      | ~ v1_relat_1(C_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_151])).

tff(c_387,plain,(
    ! [B_78,A_77] :
      ( ~ r2_hidden(B_78,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_77,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_382])).

tff(c_390,plain,(
    ! [B_78,A_77] :
      ( ~ r2_hidden(B_78,k1_xboole_0)
      | ~ r2_hidden(A_77,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_142,c_20,c_20,c_387])).

tff(c_391,plain,(
    ! [A_77] : ~ r2_hidden(A_77,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_390])).

tff(c_226,plain,(
    ! [A_52] :
      ( v1_xboole_0(k1_funct_1(A_52,'#skF_1'(A_52)))
      | v2_relat_1(A_52)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_230,plain,(
    ! [A_52] :
      ( k1_funct_1(A_52,'#skF_1'(A_52)) = k1_xboole_0
      | v2_relat_1(A_52)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(resolution,[status(thm)],[c_226,c_2])).

tff(c_323,plain,(
    ! [B_64,C_65,A_66] :
      ( r2_hidden(k1_funct_1(B_64,C_65),k1_funct_1(A_66,C_65))
      | ~ r2_hidden(C_65,k1_relat_1(B_64))
      | ~ v5_funct_1(B_64,A_66)
      | ~ v1_funct_1(B_64)
      | ~ v1_relat_1(B_64)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_329,plain,(
    ! [B_64,A_52] :
      ( r2_hidden(k1_funct_1(B_64,'#skF_1'(A_52)),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_52),k1_relat_1(B_64))
      | ~ v5_funct_1(B_64,A_52)
      | ~ v1_funct_1(B_64)
      | ~ v1_relat_1(B_64)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52)
      | v2_relat_1(A_52)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_323])).

tff(c_415,plain,(
    ! [A_83,B_84] :
      ( ~ r2_hidden('#skF_1'(A_83),k1_relat_1(B_84))
      | ~ v5_funct_1(B_84,A_83)
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83)
      | v2_relat_1(A_83)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(negUnitSimplification,[status(thm)],[c_391,c_329])).

tff(c_421,plain,(
    ! [A_83] :
      ( ~ r2_hidden('#skF_1'(A_83),k1_relat_1('#skF_4'))
      | ~ v5_funct_1('#skF_3',A_83)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83)
      | v2_relat_1(A_83)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_415])).

tff(c_438,plain,(
    ! [A_86] :
      ( ~ r2_hidden('#skF_1'(A_86),k1_relat_1('#skF_4'))
      | ~ v5_funct_1('#skF_3',A_86)
      | v2_relat_1(A_86)
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_421])).

tff(c_442,plain,
    ( ~ v5_funct_1('#skF_3','#skF_4')
    | v2_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_438])).

tff(c_445,plain,(
    v2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_442])).

tff(c_447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_445])).

tff(c_448,plain,(
    ! [B_78] : ~ r2_hidden(B_78,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_497,plain,(
    ! [A_96,B_97] :
      ( ~ r2_hidden('#skF_1'(A_96),k1_relat_1(B_97))
      | ~ v5_funct_1(B_97,A_96)
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97)
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96)
      | v2_relat_1(A_96)
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(negUnitSimplification,[status(thm)],[c_448,c_329])).

tff(c_503,plain,(
    ! [A_96] :
      ( ~ r2_hidden('#skF_1'(A_96),k1_relat_1('#skF_4'))
      | ~ v5_funct_1('#skF_3',A_96)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96)
      | v2_relat_1(A_96)
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_497])).

tff(c_512,plain,(
    ! [A_98] :
      ( ~ r2_hidden('#skF_1'(A_98),k1_relat_1('#skF_4'))
      | ~ v5_funct_1('#skF_3',A_98)
      | v2_relat_1(A_98)
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_503])).

tff(c_516,plain,
    ( ~ v5_funct_1('#skF_3','#skF_4')
    | v2_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_512])).

tff(c_519,plain,(
    v2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_516])).

tff(c_521,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_519])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.39  
% 2.76/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.40  %$ v5_funct_1 > r2_hidden > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.76/1.40  
% 2.76/1.40  %Foreground sorts:
% 2.76/1.40  
% 2.76/1.40  
% 2.76/1.40  %Background operators:
% 2.76/1.40  
% 2.76/1.40  
% 2.76/1.40  %Foreground operators:
% 2.76/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.76/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.40  tff(v2_relat_1, type, v2_relat_1: $i > $o).
% 2.76/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.76/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.76/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.76/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.76/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.76/1.40  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.76/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.76/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.76/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.76/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.76/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.76/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.76/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.76/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.76/1.40  
% 2.76/1.41  tff(f_113, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v5_funct_1(A, B) & (k1_relat_1(A) = k1_relat_1(B))) => v2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_funct_1)).
% 2.76/1.41  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_relat_1(A) <=> (![B]: ~(r2_hidden(B, k1_relat_1(A)) & v1_xboole_0(k1_funct_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_funct_1)).
% 2.76/1.41  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 2.76/1.41  tff(f_42, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.76/1.41  tff(f_87, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 2.76/1.41  tff(f_51, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.76/1.41  tff(f_48, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.76/1.41  tff(f_97, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_funct_1)).
% 2.76/1.41  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.76/1.41  tff(f_38, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.76/1.41  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.76/1.41  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 2.76/1.41  tff(c_40, plain, (~v2_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.76/1.41  tff(c_48, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.76/1.41  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.76/1.41  tff(c_44, plain, (v5_funct_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.76/1.41  tff(c_26, plain, (![A_13]: (r2_hidden('#skF_1'(A_13), k1_relat_1(A_13)) | v2_relat_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.76/1.41  tff(c_52, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.76/1.41  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.76/1.41  tff(c_42, plain, (k1_relat_1('#skF_3')=k1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.76/1.41  tff(c_74, plain, (![A_37]: (k7_relat_1(A_37, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.76/1.41  tff(c_82, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_74])).
% 2.76/1.41  tff(c_91, plain, (![A_38, B_39]: (v1_relat_1(k7_relat_1(A_38, B_39)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.76/1.41  tff(c_97, plain, (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_82, c_91])).
% 2.76/1.41  tff(c_103, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_97])).
% 2.76/1.41  tff(c_129, plain, (![A_41, B_42]: (v1_funct_1(k7_relat_1(A_41, B_42)) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.76/1.41  tff(c_135, plain, (v1_funct_1(k1_xboole_0) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_82, c_129])).
% 2.76/1.41  tff(c_142, plain, (v1_funct_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_135])).
% 2.76/1.41  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.76/1.41  tff(c_16, plain, (![A_12]: (k9_relat_1(k1_xboole_0, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.76/1.41  tff(c_365, plain, (![C_73, A_74, B_75]: (k2_tarski(k1_funct_1(C_73, A_74), k1_funct_1(C_73, B_75))=k9_relat_1(C_73, k2_tarski(A_74, B_75)) | ~r2_hidden(B_75, k1_relat_1(C_73)) | ~r2_hidden(A_74, k1_relat_1(C_73)) | ~v1_funct_1(C_73) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.76/1.41  tff(c_146, plain, (![A_43, B_44]: (k2_xboole_0(k1_tarski(A_43), k1_tarski(B_44))=k2_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.76/1.41  tff(c_10, plain, (![A_7, B_8]: (k2_xboole_0(k1_tarski(A_7), B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.76/1.41  tff(c_151, plain, (![A_43, B_44]: (k2_tarski(A_43, B_44)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_146, c_10])).
% 2.76/1.41  tff(c_382, plain, (![C_76, A_77, B_78]: (k9_relat_1(C_76, k2_tarski(A_77, B_78))!=k1_xboole_0 | ~r2_hidden(B_78, k1_relat_1(C_76)) | ~r2_hidden(A_77, k1_relat_1(C_76)) | ~v1_funct_1(C_76) | ~v1_relat_1(C_76))), inference(superposition, [status(thm), theory('equality')], [c_365, c_151])).
% 2.76/1.41  tff(c_387, plain, (![B_78, A_77]: (~r2_hidden(B_78, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_77, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_382])).
% 2.76/1.41  tff(c_390, plain, (![B_78, A_77]: (~r2_hidden(B_78, k1_xboole_0) | ~r2_hidden(A_77, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_142, c_20, c_20, c_387])).
% 2.76/1.41  tff(c_391, plain, (![A_77]: (~r2_hidden(A_77, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_390])).
% 2.76/1.41  tff(c_226, plain, (![A_52]: (v1_xboole_0(k1_funct_1(A_52, '#skF_1'(A_52))) | v2_relat_1(A_52) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.76/1.41  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.76/1.41  tff(c_230, plain, (![A_52]: (k1_funct_1(A_52, '#skF_1'(A_52))=k1_xboole_0 | v2_relat_1(A_52) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(resolution, [status(thm)], [c_226, c_2])).
% 2.76/1.41  tff(c_323, plain, (![B_64, C_65, A_66]: (r2_hidden(k1_funct_1(B_64, C_65), k1_funct_1(A_66, C_65)) | ~r2_hidden(C_65, k1_relat_1(B_64)) | ~v5_funct_1(B_64, A_66) | ~v1_funct_1(B_64) | ~v1_relat_1(B_64) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.76/1.41  tff(c_329, plain, (![B_64, A_52]: (r2_hidden(k1_funct_1(B_64, '#skF_1'(A_52)), k1_xboole_0) | ~r2_hidden('#skF_1'(A_52), k1_relat_1(B_64)) | ~v5_funct_1(B_64, A_52) | ~v1_funct_1(B_64) | ~v1_relat_1(B_64) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52) | v2_relat_1(A_52) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(superposition, [status(thm), theory('equality')], [c_230, c_323])).
% 2.76/1.41  tff(c_415, plain, (![A_83, B_84]: (~r2_hidden('#skF_1'(A_83), k1_relat_1(B_84)) | ~v5_funct_1(B_84, A_83) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83) | v2_relat_1(A_83) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(negUnitSimplification, [status(thm)], [c_391, c_329])).
% 2.76/1.41  tff(c_421, plain, (![A_83]: (~r2_hidden('#skF_1'(A_83), k1_relat_1('#skF_4')) | ~v5_funct_1('#skF_3', A_83) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(A_83) | ~v1_relat_1(A_83) | v2_relat_1(A_83) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(superposition, [status(thm), theory('equality')], [c_42, c_415])).
% 2.76/1.41  tff(c_438, plain, (![A_86]: (~r2_hidden('#skF_1'(A_86), k1_relat_1('#skF_4')) | ~v5_funct_1('#skF_3', A_86) | v2_relat_1(A_86) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_421])).
% 2.76/1.41  tff(c_442, plain, (~v5_funct_1('#skF_3', '#skF_4') | v2_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_438])).
% 2.76/1.41  tff(c_445, plain, (v2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_442])).
% 2.76/1.41  tff(c_447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_445])).
% 2.76/1.41  tff(c_448, plain, (![B_78]: (~r2_hidden(B_78, k1_xboole_0))), inference(splitRight, [status(thm)], [c_390])).
% 2.76/1.41  tff(c_497, plain, (![A_96, B_97]: (~r2_hidden('#skF_1'(A_96), k1_relat_1(B_97)) | ~v5_funct_1(B_97, A_96) | ~v1_funct_1(B_97) | ~v1_relat_1(B_97) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96) | v2_relat_1(A_96) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(negUnitSimplification, [status(thm)], [c_448, c_329])).
% 2.76/1.41  tff(c_503, plain, (![A_96]: (~r2_hidden('#skF_1'(A_96), k1_relat_1('#skF_4')) | ~v5_funct_1('#skF_3', A_96) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(A_96) | ~v1_relat_1(A_96) | v2_relat_1(A_96) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(superposition, [status(thm), theory('equality')], [c_42, c_497])).
% 2.76/1.41  tff(c_512, plain, (![A_98]: (~r2_hidden('#skF_1'(A_98), k1_relat_1('#skF_4')) | ~v5_funct_1('#skF_3', A_98) | v2_relat_1(A_98) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_503])).
% 2.76/1.41  tff(c_516, plain, (~v5_funct_1('#skF_3', '#skF_4') | v2_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_512])).
% 2.76/1.41  tff(c_519, plain, (v2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_516])).
% 2.76/1.41  tff(c_521, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_519])).
% 2.76/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.41  
% 2.76/1.41  Inference rules
% 2.76/1.41  ----------------------
% 2.76/1.41  #Ref     : 0
% 2.76/1.41  #Sup     : 102
% 2.76/1.41  #Fact    : 0
% 2.76/1.41  #Define  : 0
% 2.76/1.41  #Split   : 4
% 2.76/1.41  #Chain   : 0
% 2.76/1.41  #Close   : 0
% 2.76/1.41  
% 2.76/1.41  Ordering : KBO
% 2.76/1.41  
% 2.76/1.41  Simplification rules
% 2.76/1.41  ----------------------
% 2.76/1.41  #Subsume      : 9
% 2.76/1.41  #Demod        : 87
% 2.76/1.41  #Tautology    : 52
% 2.76/1.41  #SimpNegUnit  : 8
% 2.76/1.41  #BackRed      : 2
% 2.76/1.41  
% 2.76/1.41  #Partial instantiations: 0
% 2.76/1.41  #Strategies tried      : 1
% 2.76/1.41  
% 2.76/1.41  Timing (in seconds)
% 2.76/1.41  ----------------------
% 2.76/1.41  Preprocessing        : 0.31
% 2.76/1.41  Parsing              : 0.16
% 2.76/1.41  CNF conversion       : 0.02
% 2.76/1.41  Main loop            : 0.32
% 2.76/1.41  Inferencing          : 0.13
% 2.76/1.41  Reduction            : 0.10
% 2.76/1.41  Demodulation         : 0.07
% 2.76/1.41  BG Simplification    : 0.02
% 2.76/1.41  Subsumption          : 0.05
% 2.76/1.41  Abstraction          : 0.02
% 2.76/1.42  MUC search           : 0.00
% 2.76/1.42  Cooper               : 0.00
% 2.76/1.42  Total                : 0.66
% 2.76/1.42  Index Insertion      : 0.00
% 2.76/1.42  Index Deletion       : 0.00
% 2.76/1.42  Index Matching       : 0.00
% 2.76/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
