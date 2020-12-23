%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0716+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:45 EST 2020

% Result     : Theorem 7.88s
% Output     : CNFRefutation 7.88s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 236 expanded)
%              Number of leaves         :   24 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          :  267 ( 756 expanded)
%              Number of equality atoms :    3 (   9 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( r1_tarski(C,k1_relat_1(k5_relat_1(A,B)))
              <=> ( r1_tarski(C,k1_relat_1(A))
                  & r1_tarski(k9_relat_1(A,C),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(c_30,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_5'(A_43,B_44),A_43)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_58,plain,(
    ! [A_58,B_59] :
      ( ~ r2_hidden('#skF_5'(A_58,B_59),B_59)
      | r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_63,plain,(
    ! [A_43] : r1_tarski(A_43,A_43) ),
    inference(resolution,[status(thm)],[c_30,c_58])).

tff(c_40,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_56,plain,
    ( r1_tarski('#skF_8',k1_relat_1('#skF_6'))
    | r1_tarski('#skF_9',k1_relat_1(k5_relat_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_69,plain,(
    r1_tarski('#skF_9',k1_relat_1(k5_relat_1('#skF_6','#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_65,plain,(
    ! [C_61,B_62,A_63] :
      ( r2_hidden(C_61,B_62)
      | ~ r2_hidden(C_61,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_72,plain,(
    ! [A_64,B_65,B_66] :
      ( r2_hidden('#skF_5'(A_64,B_65),B_66)
      | ~ r1_tarski(A_64,B_66)
      | r1_tarski(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_30,c_65])).

tff(c_26,plain,(
    ! [C_47,B_44,A_43] :
      ( r2_hidden(C_47,B_44)
      | ~ r2_hidden(C_47,A_43)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_83,plain,(
    ! [A_67,B_68,B_69,B_70] :
      ( r2_hidden('#skF_5'(A_67,B_68),B_69)
      | ~ r1_tarski(B_70,B_69)
      | ~ r1_tarski(A_67,B_70)
      | r1_tarski(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_72,c_26])).

tff(c_88,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_5'(A_67,B_68),k1_relat_1(k5_relat_1('#skF_6','#skF_7')))
      | ~ r1_tarski(A_67,'#skF_9')
      | r1_tarski(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_69,c_83])).

tff(c_131,plain,(
    ! [A_86,C_87,B_88] :
      ( r2_hidden(A_86,k1_relat_1(C_87))
      | ~ r2_hidden(A_86,k1_relat_1(k5_relat_1(C_87,B_88)))
      | ~ v1_funct_1(C_87)
      | ~ v1_relat_1(C_87)
      | ~ v1_funct_1(B_88)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_138,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_5'(A_67,B_68),k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r1_tarski(A_67,'#skF_9')
      | r1_tarski(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_88,c_131])).

tff(c_153,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_5'(A_89,B_90),k1_relat_1('#skF_6'))
      | ~ r1_tarski(A_89,'#skF_9')
      | r1_tarski(A_89,B_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_44,c_42,c_138])).

tff(c_28,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden('#skF_5'(A_43,B_44),B_44)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_162,plain,(
    ! [A_91] :
      ( ~ r1_tarski(A_91,'#skF_9')
      | r1_tarski(A_91,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_153,c_28])).

tff(c_50,plain,
    ( r1_tarski('#skF_8',k1_relat_1('#skF_6'))
    | ~ r1_tarski(k9_relat_1('#skF_6','#skF_9'),k1_relat_1('#skF_7'))
    | ~ r1_tarski('#skF_9',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_82,plain,(
    ~ r1_tarski('#skF_9',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_172,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_162,c_82])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_172])).

tff(c_181,plain,(
    r1_tarski('#skF_9',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_318,plain,(
    ! [A_122,B_123,D_124] :
      ( r2_hidden('#skF_4'(A_122,B_123,k9_relat_1(A_122,B_123),D_124),B_123)
      | ~ r2_hidden(D_124,k9_relat_1(A_122,B_123))
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_418,plain,(
    ! [A_151,B_152,D_153,B_154] :
      ( r2_hidden('#skF_4'(A_151,B_152,k9_relat_1(A_151,B_152),D_153),B_154)
      | ~ r1_tarski(B_152,B_154)
      | ~ r2_hidden(D_153,k9_relat_1(A_151,B_152))
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151) ) ),
    inference(resolution,[status(thm)],[c_318,c_26])).

tff(c_806,plain,(
    ! [B_219,D_215,A_217,B_216,B_218] :
      ( r2_hidden('#skF_4'(A_217,B_216,k9_relat_1(A_217,B_216),D_215),B_218)
      | ~ r1_tarski(B_219,B_218)
      | ~ r1_tarski(B_216,B_219)
      | ~ r2_hidden(D_215,k9_relat_1(A_217,B_216))
      | ~ v1_funct_1(A_217)
      | ~ v1_relat_1(A_217) ) ),
    inference(resolution,[status(thm)],[c_418,c_26])).

tff(c_823,plain,(
    ! [A_217,B_216,D_215] :
      ( r2_hidden('#skF_4'(A_217,B_216,k9_relat_1(A_217,B_216),D_215),k1_relat_1(k5_relat_1('#skF_6','#skF_7')))
      | ~ r1_tarski(B_216,'#skF_9')
      | ~ r2_hidden(D_215,k9_relat_1(A_217,B_216))
      | ~ v1_funct_1(A_217)
      | ~ v1_relat_1(A_217) ) ),
    inference(resolution,[status(thm)],[c_69,c_806])).

tff(c_4,plain,(
    ! [A_1,B_24,D_39] :
      ( k1_funct_1(A_1,'#skF_4'(A_1,B_24,k9_relat_1(A_1,B_24),D_39)) = D_39
      | ~ r2_hidden(D_39,k9_relat_1(A_1,B_24))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_382,plain,(
    ! [C_141,A_142,B_143] :
      ( r2_hidden(k1_funct_1(C_141,A_142),k1_relat_1(B_143))
      | ~ r2_hidden(A_142,k1_relat_1(k5_relat_1(C_141,B_143)))
      | ~ v1_funct_1(C_141)
      | ~ v1_relat_1(C_141)
      | ~ v1_funct_1(B_143)
      | ~ v1_relat_1(B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2162,plain,(
    ! [D_346,B_347,A_348,B_349] :
      ( r2_hidden(D_346,k1_relat_1(B_347))
      | ~ r2_hidden('#skF_4'(A_348,B_349,k9_relat_1(A_348,B_349),D_346),k1_relat_1(k5_relat_1(A_348,B_347)))
      | ~ v1_funct_1(A_348)
      | ~ v1_relat_1(A_348)
      | ~ v1_funct_1(B_347)
      | ~ v1_relat_1(B_347)
      | ~ r2_hidden(D_346,k9_relat_1(A_348,B_349))
      | ~ v1_funct_1(A_348)
      | ~ v1_relat_1(A_348) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_382])).

tff(c_2178,plain,(
    ! [D_215,B_216] :
      ( r2_hidden(D_215,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r1_tarski(B_216,'#skF_9')
      | ~ r2_hidden(D_215,k9_relat_1('#skF_6',B_216))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_823,c_2162])).

tff(c_2202,plain,(
    ! [D_350,B_351] :
      ( r2_hidden(D_350,k1_relat_1('#skF_7'))
      | ~ r1_tarski(B_351,'#skF_9')
      | ~ r2_hidden(D_350,k9_relat_1('#skF_6',B_351)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_2178])).

tff(c_2509,plain,(
    ! [B_354,B_355] :
      ( r2_hidden('#skF_5'(k9_relat_1('#skF_6',B_354),B_355),k1_relat_1('#skF_7'))
      | ~ r1_tarski(B_354,'#skF_9')
      | r1_tarski(k9_relat_1('#skF_6',B_354),B_355) ) ),
    inference(resolution,[status(thm)],[c_30,c_2202])).

tff(c_2595,plain,(
    ! [B_360] :
      ( ~ r1_tarski(B_360,'#skF_9')
      | r1_tarski(k9_relat_1('#skF_6',B_360),k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2509,c_28])).

tff(c_180,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_6','#skF_9'),k1_relat_1('#skF_7'))
    | r1_tarski('#skF_8',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_182,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_9'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_2622,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_2595,c_182])).

tff(c_2640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_2622])).

tff(c_2642,plain,(
    r1_tarski(k9_relat_1('#skF_6','#skF_9'),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_46,plain,
    ( ~ r1_tarski('#skF_8',k1_relat_1(k5_relat_1('#skF_6','#skF_7')))
    | ~ r1_tarski(k9_relat_1('#skF_6','#skF_9'),k1_relat_1('#skF_7'))
    | ~ r1_tarski('#skF_9',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2691,plain,(
    ~ r1_tarski('#skF_8',k1_relat_1(k5_relat_1('#skF_6','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_2642,c_46])).

tff(c_2641,plain,(
    r1_tarski('#skF_8',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_2643,plain,(
    ! [A_361,B_362,B_363,B_364] :
      ( r2_hidden('#skF_5'(A_361,B_362),B_363)
      | ~ r1_tarski(B_364,B_363)
      | ~ r1_tarski(A_361,B_364)
      | r1_tarski(A_361,B_362) ) ),
    inference(resolution,[status(thm)],[c_72,c_26])).

tff(c_2655,plain,(
    ! [A_361,B_362] :
      ( r2_hidden('#skF_5'(A_361,B_362),k1_relat_1('#skF_6'))
      | ~ r1_tarski(A_361,'#skF_8')
      | r1_tarski(A_361,B_362) ) ),
    inference(resolution,[status(thm)],[c_2641,c_2643])).

tff(c_48,plain,
    ( r1_tarski(k9_relat_1('#skF_6','#skF_8'),k1_relat_1('#skF_7'))
    | ~ r1_tarski(k9_relat_1('#skF_6','#skF_9'),k1_relat_1('#skF_7'))
    | ~ r1_tarski('#skF_9',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2669,plain,(
    r1_tarski(k9_relat_1('#skF_6','#skF_8'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_2642,c_48])).

tff(c_2725,plain,(
    ! [A_377,E_378,B_379] :
      ( r2_hidden(k1_funct_1(A_377,E_378),k9_relat_1(A_377,B_379))
      | ~ r2_hidden(E_378,B_379)
      | ~ r2_hidden(E_378,k1_relat_1(A_377))
      | ~ v1_funct_1(A_377)
      | ~ v1_relat_1(A_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3194,plain,(
    ! [A_459,E_460,B_461,B_462] :
      ( r2_hidden(k1_funct_1(A_459,E_460),B_461)
      | ~ r1_tarski(k9_relat_1(A_459,B_462),B_461)
      | ~ r2_hidden(E_460,B_462)
      | ~ r2_hidden(E_460,k1_relat_1(A_459))
      | ~ v1_funct_1(A_459)
      | ~ v1_relat_1(A_459) ) ),
    inference(resolution,[status(thm)],[c_2725,c_26])).

tff(c_3205,plain,(
    ! [E_460] :
      ( r2_hidden(k1_funct_1('#skF_6',E_460),k1_relat_1('#skF_7'))
      | ~ r2_hidden(E_460,'#skF_8')
      | ~ r2_hidden(E_460,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2669,c_3194])).

tff(c_3216,plain,(
    ! [E_460] :
      ( r2_hidden(k1_funct_1('#skF_6',E_460),k1_relat_1('#skF_7'))
      | ~ r2_hidden(E_460,'#skF_8')
      | ~ r2_hidden(E_460,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_3205])).

tff(c_3327,plain,(
    ! [A_475,C_476,B_477] :
      ( r2_hidden(A_475,k1_relat_1(k5_relat_1(C_476,B_477)))
      | ~ r2_hidden(k1_funct_1(C_476,A_475),k1_relat_1(B_477))
      | ~ r2_hidden(A_475,k1_relat_1(C_476))
      | ~ v1_funct_1(C_476)
      | ~ v1_relat_1(C_476)
      | ~ v1_funct_1(B_477)
      | ~ v1_relat_1(B_477) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3341,plain,(
    ! [E_460] :
      ( r2_hidden(E_460,k1_relat_1(k5_relat_1('#skF_6','#skF_7')))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(E_460,'#skF_8')
      | ~ r2_hidden(E_460,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_3216,c_3327])).

tff(c_3386,plain,(
    ! [E_479] :
      ( r2_hidden(E_479,k1_relat_1(k5_relat_1('#skF_6','#skF_7')))
      | ~ r2_hidden(E_479,'#skF_8')
      | ~ r2_hidden(E_479,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_44,c_42,c_3341])).

tff(c_4082,plain,(
    ! [A_543] :
      ( r1_tarski(A_543,k1_relat_1(k5_relat_1('#skF_6','#skF_7')))
      | ~ r2_hidden('#skF_5'(A_543,k1_relat_1(k5_relat_1('#skF_6','#skF_7'))),'#skF_8')
      | ~ r2_hidden('#skF_5'(A_543,k1_relat_1(k5_relat_1('#skF_6','#skF_7'))),k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_3386,c_28])).

tff(c_4173,plain,(
    ! [A_548] :
      ( ~ r2_hidden('#skF_5'(A_548,k1_relat_1(k5_relat_1('#skF_6','#skF_7'))),'#skF_8')
      | ~ r1_tarski(A_548,'#skF_8')
      | r1_tarski(A_548,k1_relat_1(k5_relat_1('#skF_6','#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_2655,c_4082])).

tff(c_4201,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | r1_tarski('#skF_8',k1_relat_1(k5_relat_1('#skF_6','#skF_7'))) ),
    inference(resolution,[status(thm)],[c_30,c_4173])).

tff(c_4211,plain,(
    r1_tarski('#skF_8',k1_relat_1(k5_relat_1('#skF_6','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_4201])).

tff(c_4213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2691,c_4211])).

tff(c_4215,plain,(
    ~ r1_tarski('#skF_9',k1_relat_1(k5_relat_1('#skF_6','#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_52,plain,
    ( ~ r1_tarski('#skF_8',k1_relat_1(k5_relat_1('#skF_6','#skF_7')))
    | r1_tarski('#skF_9',k1_relat_1(k5_relat_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4216,plain,(
    ~ r1_tarski('#skF_8',k1_relat_1(k5_relat_1('#skF_6','#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_4214,plain,(
    r1_tarski('#skF_8',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_4217,plain,(
    ! [A_549,B_550,B_551] :
      ( r2_hidden('#skF_5'(A_549,B_550),B_551)
      | ~ r1_tarski(A_549,B_551)
      | r1_tarski(A_549,B_550) ) ),
    inference(resolution,[status(thm)],[c_30,c_65])).

tff(c_4228,plain,(
    ! [A_552,B_553,B_554,B_555] :
      ( r2_hidden('#skF_5'(A_552,B_553),B_554)
      | ~ r1_tarski(B_555,B_554)
      | ~ r1_tarski(A_552,B_555)
      | r1_tarski(A_552,B_553) ) ),
    inference(resolution,[status(thm)],[c_4217,c_26])).

tff(c_4236,plain,(
    ! [A_552,B_553] :
      ( r2_hidden('#skF_5'(A_552,B_553),k1_relat_1('#skF_6'))
      | ~ r1_tarski(A_552,'#skF_8')
      | r1_tarski(A_552,B_553) ) ),
    inference(resolution,[status(thm)],[c_4214,c_4228])).

tff(c_54,plain,
    ( r1_tarski(k9_relat_1('#skF_6','#skF_8'),k1_relat_1('#skF_7'))
    | r1_tarski('#skF_9',k1_relat_1(k5_relat_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4226,plain,(
    r1_tarski(k9_relat_1('#skF_6','#skF_8'),k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_4215,c_54])).

tff(c_4349,plain,(
    ! [A_581,E_582,B_583] :
      ( r2_hidden(k1_funct_1(A_581,E_582),k9_relat_1(A_581,B_583))
      | ~ r2_hidden(E_582,B_583)
      | ~ r2_hidden(E_582,k1_relat_1(A_581))
      | ~ v1_funct_1(A_581)
      | ~ v1_relat_1(A_581) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4465,plain,(
    ! [A_617,E_618,B_619,B_620] :
      ( r2_hidden(k1_funct_1(A_617,E_618),B_619)
      | ~ r1_tarski(k9_relat_1(A_617,B_620),B_619)
      | ~ r2_hidden(E_618,B_620)
      | ~ r2_hidden(E_618,k1_relat_1(A_617))
      | ~ v1_funct_1(A_617)
      | ~ v1_relat_1(A_617) ) ),
    inference(resolution,[status(thm)],[c_4349,c_26])).

tff(c_4470,plain,(
    ! [E_618] :
      ( r2_hidden(k1_funct_1('#skF_6',E_618),k1_relat_1('#skF_7'))
      | ~ r2_hidden(E_618,'#skF_8')
      | ~ r2_hidden(E_618,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4226,c_4465])).

tff(c_4479,plain,(
    ! [E_621] :
      ( r2_hidden(k1_funct_1('#skF_6',E_621),k1_relat_1('#skF_7'))
      | ~ r2_hidden(E_621,'#skF_8')
      | ~ r2_hidden(E_621,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_4470])).

tff(c_32,plain,(
    ! [A_48,C_51,B_49] :
      ( r2_hidden(A_48,k1_relat_1(k5_relat_1(C_51,B_49)))
      | ~ r2_hidden(k1_funct_1(C_51,A_48),k1_relat_1(B_49))
      | ~ r2_hidden(A_48,k1_relat_1(C_51))
      | ~ v1_funct_1(C_51)
      | ~ v1_relat_1(C_51)
      | ~ v1_funct_1(B_49)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4482,plain,(
    ! [E_621] :
      ( r2_hidden(E_621,k1_relat_1(k5_relat_1('#skF_6','#skF_7')))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(E_621,'#skF_8')
      | ~ r2_hidden(E_621,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_4479,c_32])).

tff(c_4517,plain,(
    ! [E_624] :
      ( r2_hidden(E_624,k1_relat_1(k5_relat_1('#skF_6','#skF_7')))
      | ~ r2_hidden(E_624,'#skF_8')
      | ~ r2_hidden(E_624,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_44,c_42,c_4482])).

tff(c_4819,plain,(
    ! [A_668] :
      ( r1_tarski(A_668,k1_relat_1(k5_relat_1('#skF_6','#skF_7')))
      | ~ r2_hidden('#skF_5'(A_668,k1_relat_1(k5_relat_1('#skF_6','#skF_7'))),'#skF_8')
      | ~ r2_hidden('#skF_5'(A_668,k1_relat_1(k5_relat_1('#skF_6','#skF_7'))),k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_4517,c_28])).

tff(c_4854,plain,(
    ! [A_669] :
      ( ~ r2_hidden('#skF_5'(A_669,k1_relat_1(k5_relat_1('#skF_6','#skF_7'))),'#skF_8')
      | ~ r1_tarski(A_669,'#skF_8')
      | r1_tarski(A_669,k1_relat_1(k5_relat_1('#skF_6','#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_4236,c_4819])).

tff(c_4870,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | r1_tarski('#skF_8',k1_relat_1(k5_relat_1('#skF_6','#skF_7'))) ),
    inference(resolution,[status(thm)],[c_30,c_4854])).

tff(c_4876,plain,(
    r1_tarski('#skF_8',k1_relat_1(k5_relat_1('#skF_6','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_4870])).

tff(c_4878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4216,c_4876])).

tff(c_4879,plain,(
    r1_tarski('#skF_9',k1_relat_1(k5_relat_1('#skF_6','#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_4881,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4215,c_4879])).

%------------------------------------------------------------------------------
