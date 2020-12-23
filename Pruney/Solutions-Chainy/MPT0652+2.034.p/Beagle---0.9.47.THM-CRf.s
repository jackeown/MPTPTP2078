%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:57 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 208 expanded)
%              Number of leaves         :   21 (  79 expanded)
%              Depth                    :   10
%              Number of atoms          :  151 ( 564 expanded)
%              Number of equality atoms :   60 ( 240 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k2_relat_1(A) = k2_relat_1(B)
               => k2_relat_1(k5_relat_1(A,C)) = k2_relat_1(k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_18,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_16] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_16)),A_16) = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_22,plain,(
    ! [A_20] :
      ( k2_relat_1(k2_funct_1(A_20)) = k1_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_16,plain,(
    ! [A_18] :
      ( v1_relat_1(k2_funct_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_17] :
      ( k5_relat_1(A_17,k6_relat_1(k2_relat_1(A_17))) = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_703,plain,(
    ! [C_54,B_55,A_56] :
      ( k1_relat_1(k5_relat_1(C_54,B_55)) = k1_relat_1(k5_relat_1(C_54,A_56))
      | k1_relat_1(B_55) != k1_relat_1(A_56)
      | ~ v1_relat_1(C_54)
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_778,plain,(
    ! [A_17,A_56] :
      ( k1_relat_1(k5_relat_1(A_17,A_56)) = k1_relat_1(A_17)
      | k1_relat_1(k6_relat_1(k2_relat_1(A_17))) != k1_relat_1(A_56)
      | ~ v1_relat_1(A_17)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_17)))
      | ~ v1_relat_1(A_56)
      | ~ v1_relat_1(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_703])).

tff(c_877,plain,(
    ! [A_59,A_60] :
      ( k1_relat_1(k5_relat_1(A_59,A_60)) = k1_relat_1(A_59)
      | k2_relat_1(A_59) != k1_relat_1(A_60)
      | ~ v1_relat_1(A_60)
      | ~ v1_relat_1(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6,c_778])).

tff(c_24,plain,(
    ! [A_20] :
      ( k1_relat_1(k2_funct_1(A_20)) = k2_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_160,plain,(
    ! [C_35,B_36,A_37] :
      ( k1_relat_1(k5_relat_1(C_35,B_36)) = k1_relat_1(k5_relat_1(C_35,A_37))
      | k1_relat_1(B_36) != k1_relat_1(A_37)
      | ~ v1_relat_1(C_35)
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_235,plain,(
    ! [A_17,A_37] :
      ( k1_relat_1(k5_relat_1(A_17,A_37)) = k1_relat_1(A_17)
      | k1_relat_1(k6_relat_1(k2_relat_1(A_17))) != k1_relat_1(A_37)
      | ~ v1_relat_1(A_17)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_17)))
      | ~ v1_relat_1(A_37)
      | ~ v1_relat_1(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_160])).

tff(c_327,plain,(
    ! [A_40,A_41] :
      ( k1_relat_1(k5_relat_1(A_40,A_41)) = k1_relat_1(A_40)
      | k2_relat_1(A_40) != k1_relat_1(A_41)
      | ~ v1_relat_1(A_41)
      | ~ v1_relat_1(A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6,c_235])).

tff(c_26,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_55,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_349,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_55])).

tff(c_384,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_349])).

tff(c_402,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_384])).

tff(c_405,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_402])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_405])).

tff(c_410,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_384])).

tff(c_509,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_410])).

tff(c_512,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_509])).

tff(c_516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_512])).

tff(c_517,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_410])).

tff(c_580,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_517])).

tff(c_584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_580])).

tff(c_586,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_899,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_877,c_586])).

tff(c_937,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_899])).

tff(c_958,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_937])).

tff(c_961,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_958])).

tff(c_965,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_961])).

tff(c_966,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_937])).

tff(c_968,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_966])).

tff(c_971,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_968])).

tff(c_975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_971])).

tff(c_977,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_966])).

tff(c_967,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_937])).

tff(c_1004,plain,(
    ! [B_61,C_62,A_63] :
      ( k2_relat_1(k5_relat_1(B_61,C_62)) = k2_relat_1(k5_relat_1(A_63,C_62))
      | k2_relat_1(B_61) != k2_relat_1(A_63)
      | ~ v1_relat_1(C_62)
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_585,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1034,plain,(
    ! [A_63] :
      ( k2_relat_1(k5_relat_1(A_63,'#skF_1')) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != k2_relat_1(A_63)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1004,c_585])).

tff(c_1086,plain,(
    ! [A_63] :
      ( k2_relat_1(k5_relat_1(A_63,'#skF_1')) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != k2_relat_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_967,c_32,c_1034])).

tff(c_1292,plain,(
    ! [A_66] :
      ( k2_relat_1(k5_relat_1(A_66,'#skF_1')) != k2_relat_1('#skF_1')
      | k2_relat_1(A_66) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_977,c_1086])).

tff(c_1304,plain,
    ( k2_relat_1(k6_relat_1(k1_relat_1('#skF_1'))) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_1')))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1292])).

tff(c_1312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_18,c_8,c_1304])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:57:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.47  
% 3.20/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.47  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.20/1.47  
% 3.20/1.47  %Foreground sorts:
% 3.20/1.47  
% 3.20/1.47  
% 3.20/1.47  %Background operators:
% 3.20/1.47  
% 3.20/1.47  
% 3.20/1.47  %Foreground operators:
% 3.20/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.20/1.47  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.20/1.47  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.20/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.20/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.20/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.20/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.47  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.20/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.47  
% 3.35/1.48  tff(f_94, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 3.35/1.48  tff(f_73, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.35/1.48  tff(f_53, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.35/1.48  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 3.35/1.48  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.35/1.48  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.35/1.48  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 3.35/1.48  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t198_relat_1)).
% 3.35/1.48  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k2_relat_1(A) = k2_relat_1(B)) => (k2_relat_1(k5_relat_1(A, C)) = k2_relat_1(k5_relat_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t199_relat_1)).
% 3.35/1.48  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.35/1.48  tff(c_18, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.35/1.48  tff(c_8, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.35/1.48  tff(c_10, plain, (![A_16]: (k5_relat_1(k6_relat_1(k1_relat_1(A_16)), A_16)=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.35/1.48  tff(c_30, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.35/1.48  tff(c_28, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.35/1.48  tff(c_22, plain, (![A_20]: (k2_relat_1(k2_funct_1(A_20))=k1_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.35/1.48  tff(c_16, plain, (![A_18]: (v1_relat_1(k2_funct_1(A_18)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.35/1.48  tff(c_6, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.35/1.48  tff(c_12, plain, (![A_17]: (k5_relat_1(A_17, k6_relat_1(k2_relat_1(A_17)))=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.35/1.48  tff(c_703, plain, (![C_54, B_55, A_56]: (k1_relat_1(k5_relat_1(C_54, B_55))=k1_relat_1(k5_relat_1(C_54, A_56)) | k1_relat_1(B_55)!=k1_relat_1(A_56) | ~v1_relat_1(C_54) | ~v1_relat_1(B_55) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.35/1.48  tff(c_778, plain, (![A_17, A_56]: (k1_relat_1(k5_relat_1(A_17, A_56))=k1_relat_1(A_17) | k1_relat_1(k6_relat_1(k2_relat_1(A_17)))!=k1_relat_1(A_56) | ~v1_relat_1(A_17) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_17))) | ~v1_relat_1(A_56) | ~v1_relat_1(A_17))), inference(superposition, [status(thm), theory('equality')], [c_12, c_703])).
% 3.35/1.48  tff(c_877, plain, (![A_59, A_60]: (k1_relat_1(k5_relat_1(A_59, A_60))=k1_relat_1(A_59) | k2_relat_1(A_59)!=k1_relat_1(A_60) | ~v1_relat_1(A_60) | ~v1_relat_1(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_6, c_778])).
% 3.35/1.48  tff(c_24, plain, (![A_20]: (k1_relat_1(k2_funct_1(A_20))=k2_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.35/1.48  tff(c_160, plain, (![C_35, B_36, A_37]: (k1_relat_1(k5_relat_1(C_35, B_36))=k1_relat_1(k5_relat_1(C_35, A_37)) | k1_relat_1(B_36)!=k1_relat_1(A_37) | ~v1_relat_1(C_35) | ~v1_relat_1(B_36) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.35/1.48  tff(c_235, plain, (![A_17, A_37]: (k1_relat_1(k5_relat_1(A_17, A_37))=k1_relat_1(A_17) | k1_relat_1(k6_relat_1(k2_relat_1(A_17)))!=k1_relat_1(A_37) | ~v1_relat_1(A_17) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_17))) | ~v1_relat_1(A_37) | ~v1_relat_1(A_17))), inference(superposition, [status(thm), theory('equality')], [c_12, c_160])).
% 3.35/1.48  tff(c_327, plain, (![A_40, A_41]: (k1_relat_1(k5_relat_1(A_40, A_41))=k1_relat_1(A_40) | k2_relat_1(A_40)!=k1_relat_1(A_41) | ~v1_relat_1(A_41) | ~v1_relat_1(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_6, c_235])).
% 3.35/1.48  tff(c_26, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.35/1.48  tff(c_55, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_26])).
% 3.35/1.48  tff(c_349, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_327, c_55])).
% 3.35/1.48  tff(c_384, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_349])).
% 3.35/1.48  tff(c_402, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_384])).
% 3.35/1.48  tff(c_405, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_402])).
% 3.35/1.49  tff(c_409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_405])).
% 3.35/1.49  tff(c_410, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_384])).
% 3.35/1.49  tff(c_509, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_410])).
% 3.35/1.49  tff(c_512, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_509])).
% 3.35/1.49  tff(c_516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_512])).
% 3.35/1.49  tff(c_517, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_410])).
% 3.35/1.49  tff(c_580, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_22, c_517])).
% 3.35/1.49  tff(c_584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_580])).
% 3.35/1.49  tff(c_586, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_26])).
% 3.35/1.49  tff(c_899, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_877, c_586])).
% 3.35/1.49  tff(c_937, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_899])).
% 3.35/1.49  tff(c_958, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_937])).
% 3.35/1.49  tff(c_961, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_958])).
% 3.35/1.49  tff(c_965, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_961])).
% 3.35/1.49  tff(c_966, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_937])).
% 3.35/1.49  tff(c_968, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_966])).
% 3.35/1.49  tff(c_971, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_22, c_968])).
% 3.35/1.49  tff(c_975, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_971])).
% 3.35/1.49  tff(c_977, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_966])).
% 3.35/1.49  tff(c_967, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_937])).
% 3.35/1.49  tff(c_1004, plain, (![B_61, C_62, A_63]: (k2_relat_1(k5_relat_1(B_61, C_62))=k2_relat_1(k5_relat_1(A_63, C_62)) | k2_relat_1(B_61)!=k2_relat_1(A_63) | ~v1_relat_1(C_62) | ~v1_relat_1(B_61) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.35/1.49  tff(c_585, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_26])).
% 3.35/1.49  tff(c_1034, plain, (![A_63]: (k2_relat_1(k5_relat_1(A_63, '#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1(A_63) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_63))), inference(superposition, [status(thm), theory('equality')], [c_1004, c_585])).
% 3.35/1.49  tff(c_1086, plain, (![A_63]: (k2_relat_1(k5_relat_1(A_63, '#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1(A_63) | ~v1_relat_1(A_63))), inference(demodulation, [status(thm), theory('equality')], [c_967, c_32, c_1034])).
% 3.35/1.49  tff(c_1292, plain, (![A_66]: (k2_relat_1(k5_relat_1(A_66, '#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(A_66)!=k1_relat_1('#skF_1') | ~v1_relat_1(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_977, c_1086])).
% 3.35/1.49  tff(c_1304, plain, (k2_relat_1(k6_relat_1(k1_relat_1('#skF_1')))!=k1_relat_1('#skF_1') | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_1'))) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10, c_1292])).
% 3.35/1.49  tff(c_1312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_18, c_8, c_1304])).
% 3.35/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.49  
% 3.35/1.49  Inference rules
% 3.35/1.49  ----------------------
% 3.35/1.49  #Ref     : 0
% 3.35/1.49  #Sup     : 284
% 3.35/1.49  #Fact    : 0
% 3.35/1.49  #Define  : 0
% 3.35/1.49  #Split   : 6
% 3.35/1.49  #Chain   : 0
% 3.35/1.49  #Close   : 0
% 3.35/1.49  
% 3.35/1.49  Ordering : KBO
% 3.35/1.49  
% 3.35/1.49  Simplification rules
% 3.35/1.49  ----------------------
% 3.35/1.49  #Subsume      : 11
% 3.35/1.49  #Demod        : 331
% 3.35/1.49  #Tautology    : 100
% 3.35/1.49  #SimpNegUnit  : 0
% 3.35/1.49  #BackRed      : 0
% 3.35/1.49  
% 3.35/1.49  #Partial instantiations: 0
% 3.35/1.49  #Strategies tried      : 1
% 3.35/1.49  
% 3.35/1.49  Timing (in seconds)
% 3.35/1.49  ----------------------
% 3.35/1.49  Preprocessing        : 0.29
% 3.35/1.49  Parsing              : 0.16
% 3.35/1.49  CNF conversion       : 0.02
% 3.35/1.49  Main loop            : 0.44
% 3.35/1.49  Inferencing          : 0.17
% 3.35/1.49  Reduction            : 0.14
% 3.35/1.49  Demodulation         : 0.11
% 3.35/1.49  BG Simplification    : 0.03
% 3.35/1.49  Subsumption          : 0.07
% 3.35/1.49  Abstraction          : 0.03
% 3.35/1.49  MUC search           : 0.00
% 3.35/1.49  Cooper               : 0.00
% 3.35/1.49  Total                : 0.76
% 3.35/1.49  Index Insertion      : 0.00
% 3.35/1.49  Index Deletion       : 0.00
% 3.35/1.49  Index Matching       : 0.00
% 3.35/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
