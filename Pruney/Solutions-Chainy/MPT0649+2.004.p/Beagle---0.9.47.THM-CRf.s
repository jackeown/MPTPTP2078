%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:44 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 254 expanded)
%              Number of leaves         :   28 ( 108 expanded)
%              Depth                    :   12
%              Number of atoms          :  168 ( 783 expanded)
%              Number of equality atoms :   23 ( 195 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_124,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k1_relat_1(B)) )
         => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
            & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k4_relat_1(A))
        & v1_funct_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( B = k4_relat_1(A)
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),B)
              <=> r2_hidden(k4_tarski(D,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_44,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_50,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_36,plain,(
    ! [A_32,C_34] :
      ( r2_hidden(k4_tarski(A_32,k1_funct_1(C_34,A_32)),C_34)
      | ~ r2_hidden(A_32,k1_relat_1(C_34))
      | ~ v1_funct_1(C_34)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_46,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_71,plain,(
    ! [A_39] :
      ( k4_relat_1(A_39) = k2_funct_1(A_39)
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_74,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_71])).

tff(c_77,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_74])).

tff(c_14,plain,(
    ! [A_18] :
      ( v1_relat_1(k4_relat_1(A_18))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_91,plain,
    ( v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_14])).

tff(c_101,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_91])).

tff(c_22,plain,(
    ! [A_21] :
      ( v1_funct_1(k4_relat_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_82,plain,
    ( v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_22])).

tff(c_95,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_82])).

tff(c_184,plain,(
    ! [C_58,D_59,A_60] :
      ( r2_hidden(k4_tarski(C_58,D_59),k4_relat_1(A_60))
      | ~ r2_hidden(k4_tarski(D_59,C_58),A_60)
      | ~ v1_relat_1(k4_relat_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_196,plain,(
    ! [C_58,D_59] :
      ( r2_hidden(k4_tarski(C_58,D_59),k2_funct_1('#skF_6'))
      | ~ r2_hidden(k4_tarski(D_59,C_58),'#skF_6')
      | ~ v1_relat_1(k4_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_184])).

tff(c_202,plain,(
    ! [C_61,D_62] :
      ( r2_hidden(k4_tarski(C_61,D_62),k2_funct_1('#skF_6'))
      | ~ r2_hidden(k4_tarski(D_62,C_61),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_101,c_77,c_196])).

tff(c_38,plain,(
    ! [C_34,A_32,B_33] :
      ( k1_funct_1(C_34,A_32) = B_33
      | ~ r2_hidden(k4_tarski(A_32,B_33),C_34)
      | ~ v1_funct_1(C_34)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_211,plain,(
    ! [C_61,D_62] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_61) = D_62
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ r2_hidden(k4_tarski(D_62,C_61),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_202,c_38])).

tff(c_231,plain,(
    ! [C_65,D_66] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_65) = D_66
      | ~ r2_hidden(k4_tarski(D_66,C_65),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_95,c_211])).

tff(c_238,plain,(
    ! [A_32] :
      ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_32)) = A_32
      | ~ r2_hidden(A_32,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_36,c_231])).

tff(c_248,plain,(
    ! [A_68] :
      ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_68)) = A_68
      | ~ r2_hidden(A_68,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_238])).

tff(c_42,plain,
    ( k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),'#skF_5') != '#skF_5'
    | k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_78,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_269,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_78])).

tff(c_285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_269])).

tff(c_287,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_300,plain,
    ( v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_14])).

tff(c_310,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_300])).

tff(c_291,plain,
    ( v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_22])).

tff(c_304,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_291])).

tff(c_370,plain,(
    ! [C_80,D_81,A_82] :
      ( r2_hidden(k4_tarski(C_80,D_81),k4_relat_1(A_82))
      | ~ r2_hidden(k4_tarski(D_81,C_80),A_82)
      | ~ v1_relat_1(k4_relat_1(A_82))
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_40,plain,(
    ! [A_32,C_34,B_33] :
      ( r2_hidden(A_32,k1_relat_1(C_34))
      | ~ r2_hidden(k4_tarski(A_32,B_33),C_34)
      | ~ v1_funct_1(C_34)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_715,plain,(
    ! [C_112,A_113,D_114] :
      ( r2_hidden(C_112,k1_relat_1(k4_relat_1(A_113)))
      | ~ v1_funct_1(k4_relat_1(A_113))
      | ~ r2_hidden(k4_tarski(D_114,C_112),A_113)
      | ~ v1_relat_1(k4_relat_1(A_113))
      | ~ v1_relat_1(A_113) ) ),
    inference(resolution,[status(thm)],[c_370,c_40])).

tff(c_746,plain,(
    ! [C_34,A_32] :
      ( r2_hidden(k1_funct_1(C_34,A_32),k1_relat_1(k4_relat_1(C_34)))
      | ~ v1_funct_1(k4_relat_1(C_34))
      | ~ v1_relat_1(k4_relat_1(C_34))
      | ~ r2_hidden(A_32,k1_relat_1(C_34))
      | ~ v1_funct_1(C_34)
      | ~ v1_relat_1(C_34) ) ),
    inference(resolution,[status(thm)],[c_36,c_715])).

tff(c_1084,plain,(
    ! [A_138,C_139,B_140] :
      ( r2_hidden(A_138,k1_relat_1(k5_relat_1(C_139,B_140)))
      | ~ r2_hidden(k1_funct_1(C_139,A_138),k1_relat_1(B_140))
      | ~ r2_hidden(A_138,k1_relat_1(C_139))
      | ~ v1_funct_1(C_139)
      | ~ v1_relat_1(C_139)
      | ~ v1_funct_1(B_140)
      | ~ v1_relat_1(B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1300,plain,(
    ! [A_146,C_147] :
      ( r2_hidden(A_146,k1_relat_1(k5_relat_1(C_147,k4_relat_1(C_147))))
      | ~ v1_funct_1(k4_relat_1(C_147))
      | ~ v1_relat_1(k4_relat_1(C_147))
      | ~ r2_hidden(A_146,k1_relat_1(C_147))
      | ~ v1_funct_1(C_147)
      | ~ v1_relat_1(C_147) ) ),
    inference(resolution,[status(thm)],[c_746,c_1084])).

tff(c_1347,plain,(
    ! [A_146] :
      ( r2_hidden(A_146,k1_relat_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6'))))
      | ~ v1_funct_1(k4_relat_1('#skF_6'))
      | ~ v1_relat_1(k4_relat_1('#skF_6'))
      | ~ r2_hidden(A_146,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_1300])).

tff(c_1372,plain,(
    ! [A_148] :
      ( r2_hidden(A_148,k1_relat_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6'))))
      | ~ r2_hidden(A_148,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_310,c_77,c_304,c_77,c_1347])).

tff(c_34,plain,(
    ! [C_31,B_29,A_28] :
      ( k1_funct_1(k5_relat_1(C_31,B_29),A_28) = k1_funct_1(B_29,k1_funct_1(C_31,A_28))
      | ~ r2_hidden(A_28,k1_relat_1(k5_relat_1(C_31,B_29)))
      | ~ v1_funct_1(C_31)
      | ~ v1_relat_1(C_31)
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1383,plain,(
    ! [A_148] :
      ( k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),A_148) = k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_148))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ r2_hidden(A_148,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1372,c_34])).

tff(c_1422,plain,(
    ! [A_149] :
      ( k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),A_149) = k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_149))
      | ~ r2_hidden(A_149,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_304,c_50,c_48,c_1383])).

tff(c_286,plain,(
    k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1446,plain,
    ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5'
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1422,c_286])).

tff(c_1453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_287,c_1446])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:01:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.59  
% 3.44/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.59  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 3.44/1.59  
% 3.44/1.59  %Foreground sorts:
% 3.44/1.59  
% 3.44/1.59  
% 3.44/1.59  %Background operators:
% 3.44/1.59  
% 3.44/1.59  
% 3.44/1.59  %Foreground operators:
% 3.44/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.44/1.59  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.44/1.59  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.44/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.44/1.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.44/1.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.44/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.44/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.44/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.44/1.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.44/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.44/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.44/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.44/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.44/1.59  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.44/1.59  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.44/1.59  
% 3.44/1.60  tff(f_124, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 3.44/1.60  tff(f_111, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.44/1.60  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 3.44/1.60  tff(f_41, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.44/1.60  tff(f_65, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => (v1_relat_1(k4_relat_1(A)) & v1_funct_1(k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_funct_1)).
% 3.44/1.61  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((B = k4_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> r2_hidden(k4_tarski(D, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_relat_1)).
% 3.44/1.61  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 3.44/1.61  tff(f_101, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 3.44/1.61  tff(c_44, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.44/1.61  tff(c_50, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.44/1.61  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.44/1.61  tff(c_36, plain, (![A_32, C_34]: (r2_hidden(k4_tarski(A_32, k1_funct_1(C_34, A_32)), C_34) | ~r2_hidden(A_32, k1_relat_1(C_34)) | ~v1_funct_1(C_34) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.44/1.61  tff(c_46, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.44/1.61  tff(c_71, plain, (![A_39]: (k4_relat_1(A_39)=k2_funct_1(A_39) | ~v2_funct_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.44/1.61  tff(c_74, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_71])).
% 3.44/1.61  tff(c_77, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_74])).
% 3.44/1.61  tff(c_14, plain, (![A_18]: (v1_relat_1(k4_relat_1(A_18)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.44/1.61  tff(c_91, plain, (v1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_77, c_14])).
% 3.44/1.61  tff(c_101, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_91])).
% 3.44/1.61  tff(c_22, plain, (![A_21]: (v1_funct_1(k4_relat_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.44/1.61  tff(c_82, plain, (v1_funct_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_77, c_22])).
% 3.44/1.61  tff(c_95, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_82])).
% 3.44/1.61  tff(c_184, plain, (![C_58, D_59, A_60]: (r2_hidden(k4_tarski(C_58, D_59), k4_relat_1(A_60)) | ~r2_hidden(k4_tarski(D_59, C_58), A_60) | ~v1_relat_1(k4_relat_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.44/1.61  tff(c_196, plain, (![C_58, D_59]: (r2_hidden(k4_tarski(C_58, D_59), k2_funct_1('#skF_6')) | ~r2_hidden(k4_tarski(D_59, C_58), '#skF_6') | ~v1_relat_1(k4_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_184])).
% 3.44/1.61  tff(c_202, plain, (![C_61, D_62]: (r2_hidden(k4_tarski(C_61, D_62), k2_funct_1('#skF_6')) | ~r2_hidden(k4_tarski(D_62, C_61), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_101, c_77, c_196])).
% 3.44/1.61  tff(c_38, plain, (![C_34, A_32, B_33]: (k1_funct_1(C_34, A_32)=B_33 | ~r2_hidden(k4_tarski(A_32, B_33), C_34) | ~v1_funct_1(C_34) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.44/1.61  tff(c_211, plain, (![C_61, D_62]: (k1_funct_1(k2_funct_1('#skF_6'), C_61)=D_62 | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~r2_hidden(k4_tarski(D_62, C_61), '#skF_6'))), inference(resolution, [status(thm)], [c_202, c_38])).
% 3.44/1.61  tff(c_231, plain, (![C_65, D_66]: (k1_funct_1(k2_funct_1('#skF_6'), C_65)=D_66 | ~r2_hidden(k4_tarski(D_66, C_65), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_95, c_211])).
% 3.44/1.61  tff(c_238, plain, (![A_32]: (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_32))=A_32 | ~r2_hidden(A_32, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_36, c_231])).
% 3.44/1.61  tff(c_248, plain, (![A_68]: (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_68))=A_68 | ~r2_hidden(A_68, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_238])).
% 3.44/1.61  tff(c_42, plain, (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), '#skF_5')!='#skF_5' | k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.44/1.61  tff(c_78, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_42])).
% 3.44/1.61  tff(c_269, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_248, c_78])).
% 3.44/1.61  tff(c_285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_269])).
% 3.44/1.61  tff(c_287, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_42])).
% 3.44/1.61  tff(c_300, plain, (v1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_77, c_14])).
% 3.44/1.61  tff(c_310, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_300])).
% 3.44/1.61  tff(c_291, plain, (v1_funct_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_77, c_22])).
% 3.44/1.61  tff(c_304, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_291])).
% 3.44/1.61  tff(c_370, plain, (![C_80, D_81, A_82]: (r2_hidden(k4_tarski(C_80, D_81), k4_relat_1(A_82)) | ~r2_hidden(k4_tarski(D_81, C_80), A_82) | ~v1_relat_1(k4_relat_1(A_82)) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.44/1.61  tff(c_40, plain, (![A_32, C_34, B_33]: (r2_hidden(A_32, k1_relat_1(C_34)) | ~r2_hidden(k4_tarski(A_32, B_33), C_34) | ~v1_funct_1(C_34) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.44/1.61  tff(c_715, plain, (![C_112, A_113, D_114]: (r2_hidden(C_112, k1_relat_1(k4_relat_1(A_113))) | ~v1_funct_1(k4_relat_1(A_113)) | ~r2_hidden(k4_tarski(D_114, C_112), A_113) | ~v1_relat_1(k4_relat_1(A_113)) | ~v1_relat_1(A_113))), inference(resolution, [status(thm)], [c_370, c_40])).
% 3.44/1.61  tff(c_746, plain, (![C_34, A_32]: (r2_hidden(k1_funct_1(C_34, A_32), k1_relat_1(k4_relat_1(C_34))) | ~v1_funct_1(k4_relat_1(C_34)) | ~v1_relat_1(k4_relat_1(C_34)) | ~r2_hidden(A_32, k1_relat_1(C_34)) | ~v1_funct_1(C_34) | ~v1_relat_1(C_34))), inference(resolution, [status(thm)], [c_36, c_715])).
% 3.44/1.61  tff(c_1084, plain, (![A_138, C_139, B_140]: (r2_hidden(A_138, k1_relat_1(k5_relat_1(C_139, B_140))) | ~r2_hidden(k1_funct_1(C_139, A_138), k1_relat_1(B_140)) | ~r2_hidden(A_138, k1_relat_1(C_139)) | ~v1_funct_1(C_139) | ~v1_relat_1(C_139) | ~v1_funct_1(B_140) | ~v1_relat_1(B_140))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.44/1.61  tff(c_1300, plain, (![A_146, C_147]: (r2_hidden(A_146, k1_relat_1(k5_relat_1(C_147, k4_relat_1(C_147)))) | ~v1_funct_1(k4_relat_1(C_147)) | ~v1_relat_1(k4_relat_1(C_147)) | ~r2_hidden(A_146, k1_relat_1(C_147)) | ~v1_funct_1(C_147) | ~v1_relat_1(C_147))), inference(resolution, [status(thm)], [c_746, c_1084])).
% 3.44/1.61  tff(c_1347, plain, (![A_146]: (r2_hidden(A_146, k1_relat_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')))) | ~v1_funct_1(k4_relat_1('#skF_6')) | ~v1_relat_1(k4_relat_1('#skF_6')) | ~r2_hidden(A_146, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_1300])).
% 3.44/1.61  tff(c_1372, plain, (![A_148]: (r2_hidden(A_148, k1_relat_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')))) | ~r2_hidden(A_148, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_310, c_77, c_304, c_77, c_1347])).
% 3.44/1.61  tff(c_34, plain, (![C_31, B_29, A_28]: (k1_funct_1(k5_relat_1(C_31, B_29), A_28)=k1_funct_1(B_29, k1_funct_1(C_31, A_28)) | ~r2_hidden(A_28, k1_relat_1(k5_relat_1(C_31, B_29))) | ~v1_funct_1(C_31) | ~v1_relat_1(C_31) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.44/1.61  tff(c_1383, plain, (![A_148]: (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), A_148)=k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_148)) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~r2_hidden(A_148, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_1372, c_34])).
% 3.44/1.61  tff(c_1422, plain, (![A_149]: (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), A_149)=k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_149)) | ~r2_hidden(A_149, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_304, c_50, c_48, c_1383])).
% 3.44/1.61  tff(c_286, plain, (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_42])).
% 3.44/1.61  tff(c_1446, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5' | ~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1422, c_286])).
% 3.44/1.61  tff(c_1453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_287, c_1446])).
% 3.44/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.61  
% 3.44/1.61  Inference rules
% 3.44/1.61  ----------------------
% 3.44/1.61  #Ref     : 0
% 3.44/1.61  #Sup     : 288
% 3.44/1.61  #Fact    : 0
% 3.44/1.61  #Define  : 0
% 3.44/1.61  #Split   : 4
% 3.44/1.61  #Chain   : 0
% 3.44/1.61  #Close   : 0
% 3.44/1.61  
% 3.44/1.61  Ordering : KBO
% 3.44/1.61  
% 3.44/1.61  Simplification rules
% 3.44/1.61  ----------------------
% 3.44/1.61  #Subsume      : 38
% 3.44/1.61  #Demod        : 419
% 3.44/1.61  #Tautology    : 100
% 3.44/1.61  #SimpNegUnit  : 0
% 3.44/1.61  #BackRed      : 0
% 3.44/1.61  
% 3.44/1.61  #Partial instantiations: 0
% 3.44/1.61  #Strategies tried      : 1
% 3.44/1.61  
% 3.44/1.61  Timing (in seconds)
% 3.44/1.61  ----------------------
% 3.44/1.61  Preprocessing        : 0.34
% 3.44/1.61  Parsing              : 0.18
% 3.44/1.61  CNF conversion       : 0.03
% 3.44/1.61  Main loop            : 0.48
% 3.44/1.61  Inferencing          : 0.18
% 3.44/1.61  Reduction            : 0.15
% 3.44/1.61  Demodulation         : 0.11
% 3.44/1.61  BG Simplification    : 0.03
% 3.44/1.61  Subsumption          : 0.09
% 3.44/1.61  Abstraction          : 0.03
% 3.44/1.61  MUC search           : 0.00
% 3.44/1.61  Cooper               : 0.00
% 3.44/1.61  Total                : 0.86
% 3.44/1.61  Index Insertion      : 0.00
% 3.44/1.61  Index Deletion       : 0.00
% 3.44/1.61  Index Matching       : 0.00
% 3.44/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
