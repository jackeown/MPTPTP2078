%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:56 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 178 expanded)
%              Number of leaves         :   23 (  69 expanded)
%              Depth                    :   10
%              Number of atoms          :  145 ( 479 expanded)
%              Number of equality atoms :   56 ( 199 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k2_relat_1(A) = k2_relat_1(B)
               => k2_relat_1(k5_relat_1(A,C)) = k2_relat_1(k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_28,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_22,plain,(
    ! [A_22] :
      ( k2_relat_1(k2_funct_1(A_22)) = k1_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16,plain,(
    ! [A_20] :
      ( k7_relat_1(A_20,k1_relat_1(A_20)) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    ! [A_21] :
      ( v1_relat_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [A_18,B_19] :
      ( k5_relat_1(k6_relat_1(A_18),B_19) = k7_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_736,plain,(
    ! [B_61,C_62,A_63] :
      ( k2_relat_1(k5_relat_1(B_61,C_62)) = k2_relat_1(k5_relat_1(A_63,C_62))
      | k2_relat_1(B_61) != k2_relat_1(A_63)
      | ~ v1_relat_1(C_62)
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_775,plain,(
    ! [B_19,A_18,A_63] :
      ( k2_relat_1(k7_relat_1(B_19,A_18)) = k2_relat_1(k5_relat_1(A_63,B_19))
      | k2_relat_1(k6_relat_1(A_18)) != k2_relat_1(A_63)
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(A_63)
      | ~ v1_relat_1(B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_736])).

tff(c_860,plain,(
    ! [B_66,A_67,A_68] :
      ( k2_relat_1(k7_relat_1(B_66,A_67)) = k2_relat_1(k5_relat_1(A_68,B_66))
      | k2_relat_1(A_68) != A_67
      | ~ v1_relat_1(A_68)
      | ~ v1_relat_1(B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10,c_775])).

tff(c_24,plain,(
    ! [A_22] :
      ( k1_relat_1(k2_funct_1(A_22)) = k2_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_191,plain,(
    ! [C_38,B_39,A_40] :
      ( k1_relat_1(k5_relat_1(C_38,B_39)) = k1_relat_1(k5_relat_1(C_38,A_40))
      | k1_relat_1(B_39) != k1_relat_1(A_40)
      | ~ v1_relat_1(C_38)
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_76,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_215,plain,(
    ! [A_40] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),A_40)) != k2_relat_1('#skF_1')
      | k1_relat_1(A_40) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_76])).

tff(c_261,plain,(
    ! [A_40] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),A_40)) != k2_relat_1('#skF_1')
      | k1_relat_1(A_40) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_215])).

tff(c_589,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_261])).

tff(c_592,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_589])).

tff(c_596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_592])).

tff(c_598,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_261])).

tff(c_8,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_17] :
      ( k5_relat_1(A_17,k6_relat_1(k2_relat_1(A_17))) = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_254,plain,(
    ! [A_17,A_40] :
      ( k1_relat_1(k5_relat_1(A_17,A_40)) = k1_relat_1(A_17)
      | k1_relat_1(k6_relat_1(k2_relat_1(A_17))) != k1_relat_1(A_40)
      | ~ v1_relat_1(A_17)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_17)))
      | ~ v1_relat_1(A_40)
      | ~ v1_relat_1(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_191])).

tff(c_359,plain,(
    ! [A_45,A_46] :
      ( k1_relat_1(k5_relat_1(A_45,A_46)) = k1_relat_1(A_45)
      | k2_relat_1(A_45) != k1_relat_1(A_46)
      | ~ v1_relat_1(A_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_254])).

tff(c_378,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_76])).

tff(c_410,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_378])).

tff(c_588,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_410])).

tff(c_600,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_588])).

tff(c_601,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_410])).

tff(c_603,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_601])).

tff(c_606,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_603])).

tff(c_610,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_606])).

tff(c_611,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_601])).

tff(c_641,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_611])).

tff(c_645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_641])).

tff(c_646,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_885,plain,(
    ! [A_67] :
      ( k2_relat_1(k7_relat_1('#skF_1',A_67)) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != A_67
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_860,c_646])).

tff(c_919,plain,(
    ! [A_67] :
      ( k2_relat_1(k7_relat_1('#skF_1',A_67)) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != A_67
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_885])).

tff(c_932,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_919])).

tff(c_935,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_932])).

tff(c_939,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_935])).

tff(c_1024,plain,(
    ! [A_72] :
      ( k2_relat_1(k7_relat_1('#skF_1',A_72)) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != A_72 ) ),
    inference(splitRight,[status(thm)],[c_919])).

tff(c_1032,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1024])).

tff(c_1037,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1032])).

tff(c_1040,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1037])).

tff(c_1044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_1040])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:29:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.51  
% 3.13/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.51  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.13/1.51  
% 3.13/1.51  %Foreground sorts:
% 3.13/1.51  
% 3.13/1.51  
% 3.13/1.51  %Background operators:
% 3.13/1.51  
% 3.13/1.51  
% 3.13/1.51  %Foreground operators:
% 3.13/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.13/1.51  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.13/1.51  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.13/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.13/1.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.13/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.13/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.13/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.13/1.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.13/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.13/1.51  
% 3.26/1.53  tff(f_96, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 3.26/1.53  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.26/1.53  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 3.26/1.53  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.26/1.53  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.26/1.53  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.28/1.53  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.28/1.53  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k2_relat_1(A) = k2_relat_1(B)) => (k2_relat_1(k5_relat_1(A, C)) = k2_relat_1(k5_relat_1(B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t199_relat_1)).
% 3.28/1.53  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t198_relat_1)).
% 3.28/1.53  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 3.28/1.53  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.28/1.53  tff(c_30, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.28/1.53  tff(c_28, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.28/1.53  tff(c_22, plain, (![A_22]: (k2_relat_1(k2_funct_1(A_22))=k1_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.28/1.53  tff(c_16, plain, (![A_20]: (k7_relat_1(A_20, k1_relat_1(A_20))=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.28/1.53  tff(c_20, plain, (![A_21]: (v1_relat_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.28/1.53  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.28/1.53  tff(c_10, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.28/1.53  tff(c_14, plain, (![A_18, B_19]: (k5_relat_1(k6_relat_1(A_18), B_19)=k7_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.28/1.53  tff(c_736, plain, (![B_61, C_62, A_63]: (k2_relat_1(k5_relat_1(B_61, C_62))=k2_relat_1(k5_relat_1(A_63, C_62)) | k2_relat_1(B_61)!=k2_relat_1(A_63) | ~v1_relat_1(C_62) | ~v1_relat_1(B_61) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.28/1.53  tff(c_775, plain, (![B_19, A_18, A_63]: (k2_relat_1(k7_relat_1(B_19, A_18))=k2_relat_1(k5_relat_1(A_63, B_19)) | k2_relat_1(k6_relat_1(A_18))!=k2_relat_1(A_63) | ~v1_relat_1(B_19) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(A_63) | ~v1_relat_1(B_19))), inference(superposition, [status(thm), theory('equality')], [c_14, c_736])).
% 3.28/1.53  tff(c_860, plain, (![B_66, A_67, A_68]: (k2_relat_1(k7_relat_1(B_66, A_67))=k2_relat_1(k5_relat_1(A_68, B_66)) | k2_relat_1(A_68)!=A_67 | ~v1_relat_1(A_68) | ~v1_relat_1(B_66))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10, c_775])).
% 3.28/1.53  tff(c_24, plain, (![A_22]: (k1_relat_1(k2_funct_1(A_22))=k2_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.28/1.53  tff(c_191, plain, (![C_38, B_39, A_40]: (k1_relat_1(k5_relat_1(C_38, B_39))=k1_relat_1(k5_relat_1(C_38, A_40)) | k1_relat_1(B_39)!=k1_relat_1(A_40) | ~v1_relat_1(C_38) | ~v1_relat_1(B_39) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.28/1.53  tff(c_26, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.28/1.53  tff(c_76, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_26])).
% 3.28/1.53  tff(c_215, plain, (![A_40]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), A_40))!=k2_relat_1('#skF_1') | k1_relat_1(A_40)!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_191, c_76])).
% 3.28/1.53  tff(c_261, plain, (![A_40]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), A_40))!=k2_relat_1('#skF_1') | k1_relat_1(A_40)!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_215])).
% 3.28/1.53  tff(c_589, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_261])).
% 3.28/1.53  tff(c_592, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_589])).
% 3.28/1.53  tff(c_596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_592])).
% 3.28/1.53  tff(c_598, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_261])).
% 3.28/1.53  tff(c_8, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.28/1.53  tff(c_12, plain, (![A_17]: (k5_relat_1(A_17, k6_relat_1(k2_relat_1(A_17)))=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.28/1.53  tff(c_254, plain, (![A_17, A_40]: (k1_relat_1(k5_relat_1(A_17, A_40))=k1_relat_1(A_17) | k1_relat_1(k6_relat_1(k2_relat_1(A_17)))!=k1_relat_1(A_40) | ~v1_relat_1(A_17) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_17))) | ~v1_relat_1(A_40) | ~v1_relat_1(A_17))), inference(superposition, [status(thm), theory('equality')], [c_12, c_191])).
% 3.28/1.53  tff(c_359, plain, (![A_45, A_46]: (k1_relat_1(k5_relat_1(A_45, A_46))=k1_relat_1(A_45) | k2_relat_1(A_45)!=k1_relat_1(A_46) | ~v1_relat_1(A_46) | ~v1_relat_1(A_45))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_254])).
% 3.28/1.53  tff(c_378, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_359, c_76])).
% 3.28/1.53  tff(c_410, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_378])).
% 3.28/1.53  tff(c_588, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_410])).
% 3.28/1.53  tff(c_600, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_598, c_588])).
% 3.28/1.53  tff(c_601, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_410])).
% 3.28/1.53  tff(c_603, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_601])).
% 3.28/1.53  tff(c_606, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_603])).
% 3.28/1.53  tff(c_610, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_606])).
% 3.28/1.53  tff(c_611, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_601])).
% 3.28/1.53  tff(c_641, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_22, c_611])).
% 3.28/1.53  tff(c_645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_641])).
% 3.28/1.53  tff(c_646, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_26])).
% 3.28/1.53  tff(c_885, plain, (![A_67]: (k2_relat_1(k7_relat_1('#skF_1', A_67))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=A_67 | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_860, c_646])).
% 3.28/1.53  tff(c_919, plain, (![A_67]: (k2_relat_1(k7_relat_1('#skF_1', A_67))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=A_67 | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_885])).
% 3.28/1.53  tff(c_932, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_919])).
% 3.28/1.53  tff(c_935, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_932])).
% 3.28/1.53  tff(c_939, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_935])).
% 3.28/1.53  tff(c_1024, plain, (![A_72]: (k2_relat_1(k7_relat_1('#skF_1', A_72))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=A_72)), inference(splitRight, [status(thm)], [c_919])).
% 3.28/1.53  tff(c_1032, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_1024])).
% 3.28/1.53  tff(c_1037, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1032])).
% 3.28/1.53  tff(c_1040, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_22, c_1037])).
% 3.28/1.53  tff(c_1044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_1040])).
% 3.28/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.53  
% 3.28/1.53  Inference rules
% 3.28/1.53  ----------------------
% 3.28/1.53  #Ref     : 0
% 3.28/1.53  #Sup     : 227
% 3.28/1.53  #Fact    : 0
% 3.28/1.53  #Define  : 0
% 3.28/1.53  #Split   : 6
% 3.28/1.53  #Chain   : 0
% 3.28/1.53  #Close   : 0
% 3.28/1.53  
% 3.28/1.53  Ordering : KBO
% 3.28/1.53  
% 3.28/1.53  Simplification rules
% 3.28/1.53  ----------------------
% 3.28/1.53  #Subsume      : 9
% 3.28/1.53  #Demod        : 202
% 3.28/1.53  #Tautology    : 77
% 3.28/1.53  #SimpNegUnit  : 0
% 3.28/1.53  #BackRed      : 0
% 3.28/1.53  
% 3.28/1.53  #Partial instantiations: 0
% 3.28/1.53  #Strategies tried      : 1
% 3.28/1.53  
% 3.28/1.53  Timing (in seconds)
% 3.28/1.53  ----------------------
% 3.28/1.53  Preprocessing        : 0.32
% 3.28/1.53  Parsing              : 0.18
% 3.28/1.53  CNF conversion       : 0.02
% 3.28/1.53  Main loop            : 0.39
% 3.28/1.53  Inferencing          : 0.15
% 3.28/1.53  Reduction            : 0.12
% 3.28/1.53  Demodulation         : 0.09
% 3.28/1.53  BG Simplification    : 0.03
% 3.28/1.53  Subsumption          : 0.06
% 3.28/1.53  Abstraction          : 0.03
% 3.28/1.53  MUC search           : 0.00
% 3.28/1.53  Cooper               : 0.00
% 3.28/1.53  Total                : 0.74
% 3.28/1.53  Index Insertion      : 0.00
% 3.28/1.53  Index Deletion       : 0.00
% 3.28/1.53  Index Matching       : 0.00
% 3.28/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
