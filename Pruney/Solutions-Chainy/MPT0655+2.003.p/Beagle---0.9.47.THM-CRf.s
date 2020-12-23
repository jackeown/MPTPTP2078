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
% DateTime   : Thu Dec  3 10:03:59 EST 2020

% Result     : Theorem 6.14s
% Output     : CNFRefutation 6.14s
% Verified   : 
% Statistics : Number of formulae       :   57 (  99 expanded)
%              Number of leaves         :   23 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  161 ( 323 expanded)
%              Number of equality atoms :   24 (  52 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_6 > #skF_2 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( B = k2_funct_1(A)
            <=> ( k1_relat_1(B) = k2_relat_1(A)
                & ! [C,D] :
                    ( ( ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) )
                     => ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) ) )
                    & ( ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) )
                     => ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_52,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_12,plain,(
    ! [A_8] :
      ( v1_funct_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    ! [A_8] :
      ( v1_relat_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_57,plain,(
    ! [A_29] :
      ( '#skF_2'(A_29) != '#skF_1'(A_29)
      | v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_48,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_61,plain,
    ( '#skF_2'(k2_funct_1('#skF_7')) != '#skF_1'(k2_funct_1('#skF_7'))
    | ~ v1_funct_1(k2_funct_1('#skF_7'))
    | ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_57,c_48])).

tff(c_80,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_83,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_14,c_80])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_83])).

tff(c_88,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_7'))
    | '#skF_2'(k2_funct_1('#skF_7')) != '#skF_1'(k2_funct_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_90,plain,(
    '#skF_2'(k2_funct_1('#skF_7')) != '#skF_1'(k2_funct_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_50,plain,(
    v2_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_89,plain,(
    v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_46,plain,(
    ! [A_26] :
      ( k1_relat_1(k2_funct_1(A_26)) = k2_relat_1(A_26)
      | ~ v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_95,plain,(
    ! [A_33] :
      ( r2_hidden('#skF_1'(A_33),k1_relat_1(A_33))
      | v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_98,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_1'(k2_funct_1(A_26)),k2_relat_1(A_26))
      | v2_funct_1(k2_funct_1(A_26))
      | ~ v1_funct_1(k2_funct_1(A_26))
      | ~ v1_relat_1(k2_funct_1(A_26))
      | ~ v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_95])).

tff(c_91,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_2'(A_32),k1_relat_1(A_32))
      | v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_94,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_2'(k2_funct_1(A_26)),k2_relat_1(A_26))
      | v2_funct_1(k2_funct_1(A_26))
      | ~ v1_funct_1(k2_funct_1(A_26))
      | ~ v1_relat_1(k2_funct_1(A_26))
      | ~ v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_91])).

tff(c_6,plain,(
    ! [A_1] :
      ( k1_funct_1(A_1,'#skF_2'(A_1)) = k1_funct_1(A_1,'#skF_1'(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_132,plain,(
    ! [A_42,C_43] :
      ( k1_funct_1(A_42,k1_funct_1(k2_funct_1(A_42),C_43)) = C_43
      | ~ r2_hidden(C_43,k2_relat_1(A_42))
      | ~ v1_funct_1(k2_funct_1(A_42))
      | ~ v1_relat_1(k2_funct_1(A_42))
      | ~ v2_funct_1(A_42)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_383,plain,(
    ! [A_69] :
      ( k1_funct_1(A_69,k1_funct_1(k2_funct_1(A_69),'#skF_1'(k2_funct_1(A_69)))) = '#skF_2'(k2_funct_1(A_69))
      | ~ r2_hidden('#skF_2'(k2_funct_1(A_69)),k2_relat_1(A_69))
      | ~ v1_funct_1(k2_funct_1(A_69))
      | ~ v1_relat_1(k2_funct_1(A_69))
      | ~ v2_funct_1(A_69)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69)
      | v2_funct_1(k2_funct_1(A_69))
      | ~ v1_funct_1(k2_funct_1(A_69))
      | ~ v1_relat_1(k2_funct_1(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_132])).

tff(c_36,plain,(
    ! [A_9,C_24] :
      ( k1_funct_1(A_9,k1_funct_1(k2_funct_1(A_9),C_24)) = C_24
      | ~ r2_hidden(C_24,k2_relat_1(A_9))
      | ~ v1_funct_1(k2_funct_1(A_9))
      | ~ v1_relat_1(k2_funct_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2273,plain,(
    ! [A_151] :
      ( '#skF_2'(k2_funct_1(A_151)) = '#skF_1'(k2_funct_1(A_151))
      | ~ r2_hidden('#skF_1'(k2_funct_1(A_151)),k2_relat_1(A_151))
      | ~ v1_funct_1(k2_funct_1(A_151))
      | ~ v1_relat_1(k2_funct_1(A_151))
      | ~ v2_funct_1(A_151)
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151)
      | ~ r2_hidden('#skF_2'(k2_funct_1(A_151)),k2_relat_1(A_151))
      | ~ v1_funct_1(k2_funct_1(A_151))
      | ~ v1_relat_1(k2_funct_1(A_151))
      | ~ v2_funct_1(A_151)
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151)
      | v2_funct_1(k2_funct_1(A_151))
      | ~ v1_funct_1(k2_funct_1(A_151))
      | ~ v1_relat_1(k2_funct_1(A_151)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_36])).

tff(c_2286,plain,(
    ! [A_152] :
      ( '#skF_2'(k2_funct_1(A_152)) = '#skF_1'(k2_funct_1(A_152))
      | ~ r2_hidden('#skF_1'(k2_funct_1(A_152)),k2_relat_1(A_152))
      | v2_funct_1(k2_funct_1(A_152))
      | ~ v1_funct_1(k2_funct_1(A_152))
      | ~ v1_relat_1(k2_funct_1(A_152))
      | ~ v2_funct_1(A_152)
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(resolution,[status(thm)],[c_94,c_2273])).

tff(c_2307,plain,(
    ! [A_154] :
      ( '#skF_2'(k2_funct_1(A_154)) = '#skF_1'(k2_funct_1(A_154))
      | v2_funct_1(k2_funct_1(A_154))
      | ~ v1_funct_1(k2_funct_1(A_154))
      | ~ v1_relat_1(k2_funct_1(A_154))
      | ~ v2_funct_1(A_154)
      | ~ v1_funct_1(A_154)
      | ~ v1_relat_1(A_154) ) ),
    inference(resolution,[status(thm)],[c_98,c_2286])).

tff(c_2310,plain,
    ( '#skF_2'(k2_funct_1('#skF_7')) = '#skF_1'(k2_funct_1('#skF_7'))
    | ~ v1_funct_1(k2_funct_1('#skF_7'))
    | ~ v1_relat_1(k2_funct_1('#skF_7'))
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_2307,c_48])).

tff(c_2313,plain,
    ( '#skF_2'(k2_funct_1('#skF_7')) = '#skF_1'(k2_funct_1('#skF_7'))
    | ~ v1_funct_1(k2_funct_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_89,c_2310])).

tff(c_2314,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2313])).

tff(c_2317,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_2314])).

tff(c_2321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2317])).

tff(c_2322,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_2326,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_2322])).

tff(c_2330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2326])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:58:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.14/2.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.14/2.19  
% 6.14/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.14/2.19  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_6 > #skF_2 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_4
% 6.14/2.19  
% 6.14/2.19  %Foreground sorts:
% 6.14/2.19  
% 6.14/2.19  
% 6.14/2.19  %Background operators:
% 6.14/2.19  
% 6.14/2.19  
% 6.14/2.19  %Foreground operators:
% 6.14/2.19  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 6.14/2.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.14/2.19  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.14/2.19  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.14/2.19  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.14/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.14/2.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.14/2.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.14/2.19  tff('#skF_7', type, '#skF_7': $i).
% 6.14/2.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.14/2.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.14/2.19  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.14/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.14/2.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.14/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.14/2.19  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.14/2.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.14/2.19  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.14/2.19  
% 6.14/2.20  tff(f_99, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_1)).
% 6.14/2.20  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.14/2.20  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 6.14/2.20  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 6.14/2.20  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k2_funct_1(A)) <=> ((k1_relat_1(B) = k2_relat_1(A)) & (![C, D]: (((r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))) => (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))) & ((r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D))) => (r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_funct_1)).
% 6.14/2.20  tff(c_54, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.14/2.20  tff(c_52, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.14/2.20  tff(c_12, plain, (![A_8]: (v1_funct_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.14/2.20  tff(c_14, plain, (![A_8]: (v1_relat_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.14/2.20  tff(c_57, plain, (![A_29]: ('#skF_2'(A_29)!='#skF_1'(A_29) | v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.14/2.20  tff(c_48, plain, (~v2_funct_1(k2_funct_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.14/2.20  tff(c_61, plain, ('#skF_2'(k2_funct_1('#skF_7'))!='#skF_1'(k2_funct_1('#skF_7')) | ~v1_funct_1(k2_funct_1('#skF_7')) | ~v1_relat_1(k2_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_57, c_48])).
% 6.14/2.20  tff(c_80, plain, (~v1_relat_1(k2_funct_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_61])).
% 6.14/2.20  tff(c_83, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_14, c_80])).
% 6.14/2.20  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_83])).
% 6.14/2.20  tff(c_88, plain, (~v1_funct_1(k2_funct_1('#skF_7')) | '#skF_2'(k2_funct_1('#skF_7'))!='#skF_1'(k2_funct_1('#skF_7'))), inference(splitRight, [status(thm)], [c_61])).
% 6.14/2.20  tff(c_90, plain, ('#skF_2'(k2_funct_1('#skF_7'))!='#skF_1'(k2_funct_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_88])).
% 6.14/2.20  tff(c_50, plain, (v2_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.14/2.20  tff(c_89, plain, (v1_relat_1(k2_funct_1('#skF_7'))), inference(splitRight, [status(thm)], [c_61])).
% 6.14/2.20  tff(c_46, plain, (![A_26]: (k1_relat_1(k2_funct_1(A_26))=k2_relat_1(A_26) | ~v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.14/2.20  tff(c_95, plain, (![A_33]: (r2_hidden('#skF_1'(A_33), k1_relat_1(A_33)) | v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.14/2.20  tff(c_98, plain, (![A_26]: (r2_hidden('#skF_1'(k2_funct_1(A_26)), k2_relat_1(A_26)) | v2_funct_1(k2_funct_1(A_26)) | ~v1_funct_1(k2_funct_1(A_26)) | ~v1_relat_1(k2_funct_1(A_26)) | ~v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_46, c_95])).
% 6.14/2.20  tff(c_91, plain, (![A_32]: (r2_hidden('#skF_2'(A_32), k1_relat_1(A_32)) | v2_funct_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.14/2.20  tff(c_94, plain, (![A_26]: (r2_hidden('#skF_2'(k2_funct_1(A_26)), k2_relat_1(A_26)) | v2_funct_1(k2_funct_1(A_26)) | ~v1_funct_1(k2_funct_1(A_26)) | ~v1_relat_1(k2_funct_1(A_26)) | ~v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_46, c_91])).
% 6.14/2.20  tff(c_6, plain, (![A_1]: (k1_funct_1(A_1, '#skF_2'(A_1))=k1_funct_1(A_1, '#skF_1'(A_1)) | v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.14/2.20  tff(c_132, plain, (![A_42, C_43]: (k1_funct_1(A_42, k1_funct_1(k2_funct_1(A_42), C_43))=C_43 | ~r2_hidden(C_43, k2_relat_1(A_42)) | ~v1_funct_1(k2_funct_1(A_42)) | ~v1_relat_1(k2_funct_1(A_42)) | ~v2_funct_1(A_42) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.14/2.20  tff(c_383, plain, (![A_69]: (k1_funct_1(A_69, k1_funct_1(k2_funct_1(A_69), '#skF_1'(k2_funct_1(A_69))))='#skF_2'(k2_funct_1(A_69)) | ~r2_hidden('#skF_2'(k2_funct_1(A_69)), k2_relat_1(A_69)) | ~v1_funct_1(k2_funct_1(A_69)) | ~v1_relat_1(k2_funct_1(A_69)) | ~v2_funct_1(A_69) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69) | v2_funct_1(k2_funct_1(A_69)) | ~v1_funct_1(k2_funct_1(A_69)) | ~v1_relat_1(k2_funct_1(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_132])).
% 6.14/2.20  tff(c_36, plain, (![A_9, C_24]: (k1_funct_1(A_9, k1_funct_1(k2_funct_1(A_9), C_24))=C_24 | ~r2_hidden(C_24, k2_relat_1(A_9)) | ~v1_funct_1(k2_funct_1(A_9)) | ~v1_relat_1(k2_funct_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.14/2.20  tff(c_2273, plain, (![A_151]: ('#skF_2'(k2_funct_1(A_151))='#skF_1'(k2_funct_1(A_151)) | ~r2_hidden('#skF_1'(k2_funct_1(A_151)), k2_relat_1(A_151)) | ~v1_funct_1(k2_funct_1(A_151)) | ~v1_relat_1(k2_funct_1(A_151)) | ~v2_funct_1(A_151) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151) | ~r2_hidden('#skF_2'(k2_funct_1(A_151)), k2_relat_1(A_151)) | ~v1_funct_1(k2_funct_1(A_151)) | ~v1_relat_1(k2_funct_1(A_151)) | ~v2_funct_1(A_151) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151) | v2_funct_1(k2_funct_1(A_151)) | ~v1_funct_1(k2_funct_1(A_151)) | ~v1_relat_1(k2_funct_1(A_151)))), inference(superposition, [status(thm), theory('equality')], [c_383, c_36])).
% 6.14/2.20  tff(c_2286, plain, (![A_152]: ('#skF_2'(k2_funct_1(A_152))='#skF_1'(k2_funct_1(A_152)) | ~r2_hidden('#skF_1'(k2_funct_1(A_152)), k2_relat_1(A_152)) | v2_funct_1(k2_funct_1(A_152)) | ~v1_funct_1(k2_funct_1(A_152)) | ~v1_relat_1(k2_funct_1(A_152)) | ~v2_funct_1(A_152) | ~v1_funct_1(A_152) | ~v1_relat_1(A_152))), inference(resolution, [status(thm)], [c_94, c_2273])).
% 6.14/2.20  tff(c_2307, plain, (![A_154]: ('#skF_2'(k2_funct_1(A_154))='#skF_1'(k2_funct_1(A_154)) | v2_funct_1(k2_funct_1(A_154)) | ~v1_funct_1(k2_funct_1(A_154)) | ~v1_relat_1(k2_funct_1(A_154)) | ~v2_funct_1(A_154) | ~v1_funct_1(A_154) | ~v1_relat_1(A_154))), inference(resolution, [status(thm)], [c_98, c_2286])).
% 6.14/2.20  tff(c_2310, plain, ('#skF_2'(k2_funct_1('#skF_7'))='#skF_1'(k2_funct_1('#skF_7')) | ~v1_funct_1(k2_funct_1('#skF_7')) | ~v1_relat_1(k2_funct_1('#skF_7')) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_2307, c_48])).
% 6.14/2.20  tff(c_2313, plain, ('#skF_2'(k2_funct_1('#skF_7'))='#skF_1'(k2_funct_1('#skF_7')) | ~v1_funct_1(k2_funct_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_89, c_2310])).
% 6.14/2.20  tff(c_2314, plain, (~v1_funct_1(k2_funct_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_90, c_2313])).
% 6.14/2.20  tff(c_2317, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_12, c_2314])).
% 6.14/2.20  tff(c_2321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_2317])).
% 6.14/2.20  tff(c_2322, plain, (~v1_funct_1(k2_funct_1('#skF_7'))), inference(splitRight, [status(thm)], [c_88])).
% 6.14/2.20  tff(c_2326, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_12, c_2322])).
% 6.14/2.20  tff(c_2330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_2326])).
% 6.14/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.14/2.20  
% 6.14/2.20  Inference rules
% 6.14/2.20  ----------------------
% 6.14/2.20  #Ref     : 3
% 6.14/2.20  #Sup     : 646
% 6.14/2.20  #Fact    : 0
% 6.14/2.20  #Define  : 0
% 6.14/2.20  #Split   : 2
% 6.14/2.20  #Chain   : 0
% 6.14/2.20  #Close   : 0
% 6.14/2.20  
% 6.14/2.20  Ordering : KBO
% 6.14/2.20  
% 6.14/2.20  Simplification rules
% 6.14/2.20  ----------------------
% 6.14/2.20  #Subsume      : 70
% 6.14/2.20  #Demod        : 10
% 6.14/2.20  #Tautology    : 165
% 6.14/2.20  #SimpNegUnit  : 1
% 6.14/2.20  #BackRed      : 0
% 6.14/2.20  
% 6.14/2.20  #Partial instantiations: 0
% 6.14/2.20  #Strategies tried      : 1
% 6.14/2.20  
% 6.14/2.20  Timing (in seconds)
% 6.14/2.20  ----------------------
% 6.14/2.20  Preprocessing        : 0.33
% 6.14/2.20  Parsing              : 0.16
% 6.14/2.20  CNF conversion       : 0.03
% 6.14/2.20  Main loop            : 1.12
% 6.14/2.20  Inferencing          : 0.35
% 6.14/2.20  Reduction            : 0.24
% 6.14/2.20  Demodulation         : 0.16
% 6.14/2.20  BG Simplification    : 0.08
% 6.14/2.20  Subsumption          : 0.40
% 6.14/2.20  Abstraction          : 0.06
% 6.14/2.20  MUC search           : 0.00
% 6.14/2.20  Cooper               : 0.00
% 6.14/2.20  Total                : 1.47
% 6.14/2.20  Index Insertion      : 0.00
% 6.14/2.20  Index Deletion       : 0.00
% 6.14/2.20  Index Matching       : 0.00
% 6.14/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
