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
% DateTime   : Thu Dec  3 10:05:49 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 285 expanded)
%              Number of leaves         :   31 ( 107 expanded)
%              Depth                    :   16
%              Number of atoms          :  132 ( 708 expanded)
%              Number of equality atoms :   54 ( 344 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k1_funct_1 > k11_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_97,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_81,axiom,(
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

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
        & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_36,plain,(
    ! [A_24] : k1_relat_1('#skF_2'(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,(
    ! [A_24] : v1_relat_1('#skF_2'(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_115,plain,(
    ! [A_40] :
      ( k1_relat_1(A_40) != k1_xboole_0
      | k1_xboole_0 = A_40
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_121,plain,(
    ! [A_24] :
      ( k1_relat_1('#skF_2'(A_24)) != k1_xboole_0
      | '#skF_2'(A_24) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_115])).

tff(c_127,plain,(
    ! [A_24] :
      ( k1_xboole_0 != A_24
      | '#skF_2'(A_24) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_121])).

tff(c_38,plain,(
    ! [A_24] : v1_funct_1('#skF_2'(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_476,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_1'(A_76,B_77),k1_relat_1(B_77))
      | v5_funct_1(B_77,A_76)
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77)
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_485,plain,(
    ! [A_76,A_24] :
      ( r2_hidden('#skF_1'(A_76,'#skF_2'(A_24)),A_24)
      | v5_funct_1('#skF_2'(A_24),A_76)
      | ~ v1_funct_1('#skF_2'(A_24))
      | ~ v1_relat_1('#skF_2'(A_24))
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_476])).

tff(c_541,plain,(
    ! [A_84,A_85] :
      ( r2_hidden('#skF_1'(A_84,'#skF_2'(A_85)),A_85)
      | v5_funct_1('#skF_2'(A_85),A_84)
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_485])).

tff(c_151,plain,(
    ! [A_43] :
      ( k1_xboole_0 != A_43
      | '#skF_2'(A_43) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_121])).

tff(c_165,plain,(
    ! [A_43] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_43 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_40])).

tff(c_185,plain,(
    ! [A_43] : k1_xboole_0 != A_43 ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_91,plain,(
    ! [A_38] :
      ( k5_relat_1(k1_xboole_0,A_38) = k1_xboole_0
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_102,plain,(
    ! [A_24] : k5_relat_1(k1_xboole_0,'#skF_2'(A_24)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_91])).

tff(c_212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_102])).

tff(c_213,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_238,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_36])).

tff(c_288,plain,(
    ! [A_53] :
      ( k2_relat_1(A_53) = k1_xboole_0
      | k1_relat_1(A_53) != k1_xboole_0
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_291,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_213,c_288])).

tff(c_303,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_291])).

tff(c_371,plain,(
    ! [A_61,B_62] :
      ( k5_relat_1(k6_relat_1(A_61),B_62) = k7_relat_1(B_62,A_61)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [A_23] : v1_relat_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_60,plain,(
    ! [A_35] :
      ( k5_relat_1(A_35,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70,plain,(
    ! [A_23] : k5_relat_1(k6_relat_1(A_23),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_60])).

tff(c_378,plain,(
    ! [A_61] :
      ( k7_relat_1(k1_xboole_0,A_61) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_70])).

tff(c_397,plain,(
    ! [A_65] : k7_relat_1(k1_xboole_0,A_65) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_378])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( k2_relat_1(k7_relat_1(B_5,A_4)) = k9_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_402,plain,(
    ! [A_65] :
      ( k9_relat_1(k1_xboole_0,A_65) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_4])).

tff(c_410,plain,(
    ! [A_66] : k9_relat_1(k1_xboole_0,A_66) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_303,c_402])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k9_relat_1(A_1,k1_tarski(B_3)) = k11_relat_1(A_1,B_3)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_416,plain,(
    ! [B_3] :
      ( k11_relat_1(k1_xboole_0,B_3) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_2])).

tff(c_425,plain,(
    ! [B_3] : k11_relat_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_416])).

tff(c_437,plain,(
    ! [B_68,A_69] :
      ( k11_relat_1(B_68,A_69) != k1_xboole_0
      | ~ r2_hidden(A_69,k1_relat_1(B_68))
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_443,plain,(
    ! [A_24,A_69] :
      ( k11_relat_1('#skF_2'(A_24),A_69) != k1_xboole_0
      | ~ r2_hidden(A_69,A_24)
      | ~ v1_relat_1('#skF_2'(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_437])).

tff(c_460,plain,(
    ! [A_72,A_73] :
      ( k11_relat_1('#skF_2'(A_72),A_73) != k1_xboole_0
      | ~ r2_hidden(A_73,A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_443])).

tff(c_466,plain,(
    ! [A_73,A_24] :
      ( k11_relat_1(k1_xboole_0,A_73) != k1_xboole_0
      | ~ r2_hidden(A_73,A_24)
      | k1_xboole_0 != A_24 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_460])).

tff(c_469,plain,(
    ! [A_73,A_24] :
      ( ~ r2_hidden(A_73,A_24)
      | k1_xboole_0 != A_24 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_466])).

tff(c_568,plain,(
    ! [A_88,A_89] :
      ( k1_xboole_0 != A_88
      | v5_funct_1('#skF_2'(A_88),A_89)
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(resolution,[status(thm)],[c_541,c_469])).

tff(c_571,plain,(
    ! [A_24,A_89] :
      ( k1_xboole_0 != A_24
      | v5_funct_1(k1_xboole_0,A_89)
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89)
      | k1_xboole_0 != A_24 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_568])).

tff(c_572,plain,(
    ! [A_24] :
      ( k1_xboole_0 != A_24
      | k1_xboole_0 != A_24 ) ),
    inference(splitLeft,[status(thm)],[c_571])).

tff(c_578,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_572])).

tff(c_601,plain,(
    ! [A_93] :
      ( v5_funct_1(k1_xboole_0,A_93)
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(splitRight,[status(thm)],[c_571])).

tff(c_42,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_604,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_601,c_42])).

tff(c_608,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_604])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n015.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 11:18:53 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.29  
% 2.30/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.30  %$ v5_funct_1 > r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k1_funct_1 > k11_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.30/1.30  
% 2.30/1.30  %Foreground sorts:
% 2.30/1.30  
% 2.30/1.30  
% 2.30/1.30  %Background operators:
% 2.30/1.30  
% 2.30/1.30  
% 2.30/1.30  %Foreground operators:
% 2.30/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.30/1.30  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.30/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.30/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.30/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.30/1.30  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.30/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.30/1.30  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.30/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.30/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.30/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.30/1.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.30/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.30/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.30/1.30  
% 2.30/1.31  tff(f_104, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 2.30/1.31  tff(f_97, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 2.30/1.31  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.30/1.31  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 2.30/1.31  tff(f_47, axiom, (![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.30/1.31  tff(f_61, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.30/1.31  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.30/1.31  tff(f_85, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.30/1.31  tff(f_34, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.30/1.31  tff(f_30, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.30/1.31  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.30/1.31  tff(c_46, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.30/1.31  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.30/1.31  tff(c_36, plain, (![A_24]: (k1_relat_1('#skF_2'(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.30/1.31  tff(c_40, plain, (![A_24]: (v1_relat_1('#skF_2'(A_24)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.30/1.31  tff(c_115, plain, (![A_40]: (k1_relat_1(A_40)!=k1_xboole_0 | k1_xboole_0=A_40 | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.30/1.31  tff(c_121, plain, (![A_24]: (k1_relat_1('#skF_2'(A_24))!=k1_xboole_0 | '#skF_2'(A_24)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_115])).
% 2.30/1.31  tff(c_127, plain, (![A_24]: (k1_xboole_0!=A_24 | '#skF_2'(A_24)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_121])).
% 2.30/1.31  tff(c_38, plain, (![A_24]: (v1_funct_1('#skF_2'(A_24)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.30/1.31  tff(c_476, plain, (![A_76, B_77]: (r2_hidden('#skF_1'(A_76, B_77), k1_relat_1(B_77)) | v5_funct_1(B_77, A_76) | ~v1_funct_1(B_77) | ~v1_relat_1(B_77) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.30/1.31  tff(c_485, plain, (![A_76, A_24]: (r2_hidden('#skF_1'(A_76, '#skF_2'(A_24)), A_24) | v5_funct_1('#skF_2'(A_24), A_76) | ~v1_funct_1('#skF_2'(A_24)) | ~v1_relat_1('#skF_2'(A_24)) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(superposition, [status(thm), theory('equality')], [c_36, c_476])).
% 2.30/1.31  tff(c_541, plain, (![A_84, A_85]: (r2_hidden('#skF_1'(A_84, '#skF_2'(A_85)), A_85) | v5_funct_1('#skF_2'(A_85), A_84) | ~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_485])).
% 2.30/1.31  tff(c_151, plain, (![A_43]: (k1_xboole_0!=A_43 | '#skF_2'(A_43)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_121])).
% 2.30/1.31  tff(c_165, plain, (![A_43]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_43)), inference(superposition, [status(thm), theory('equality')], [c_151, c_40])).
% 2.30/1.31  tff(c_185, plain, (![A_43]: (k1_xboole_0!=A_43)), inference(splitLeft, [status(thm)], [c_165])).
% 2.30/1.31  tff(c_91, plain, (![A_38]: (k5_relat_1(k1_xboole_0, A_38)=k1_xboole_0 | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.30/1.31  tff(c_102, plain, (![A_24]: (k5_relat_1(k1_xboole_0, '#skF_2'(A_24))=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_91])).
% 2.30/1.31  tff(c_212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_102])).
% 2.30/1.31  tff(c_213, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_165])).
% 2.30/1.31  tff(c_238, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_151, c_36])).
% 2.30/1.31  tff(c_288, plain, (![A_53]: (k2_relat_1(A_53)=k1_xboole_0 | k1_relat_1(A_53)!=k1_xboole_0 | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.30/1.31  tff(c_291, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_213, c_288])).
% 2.30/1.31  tff(c_303, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_238, c_291])).
% 2.30/1.31  tff(c_371, plain, (![A_61, B_62]: (k5_relat_1(k6_relat_1(A_61), B_62)=k7_relat_1(B_62, A_61) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.30/1.31  tff(c_30, plain, (![A_23]: (v1_relat_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.30/1.31  tff(c_60, plain, (![A_35]: (k5_relat_1(A_35, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.30/1.31  tff(c_70, plain, (![A_23]: (k5_relat_1(k6_relat_1(A_23), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_60])).
% 2.30/1.31  tff(c_378, plain, (![A_61]: (k7_relat_1(k1_xboole_0, A_61)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_371, c_70])).
% 2.30/1.31  tff(c_397, plain, (![A_65]: (k7_relat_1(k1_xboole_0, A_65)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_213, c_378])).
% 2.30/1.31  tff(c_4, plain, (![B_5, A_4]: (k2_relat_1(k7_relat_1(B_5, A_4))=k9_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.30/1.31  tff(c_402, plain, (![A_65]: (k9_relat_1(k1_xboole_0, A_65)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_397, c_4])).
% 2.30/1.31  tff(c_410, plain, (![A_66]: (k9_relat_1(k1_xboole_0, A_66)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_213, c_303, c_402])).
% 2.30/1.31  tff(c_2, plain, (![A_1, B_3]: (k9_relat_1(A_1, k1_tarski(B_3))=k11_relat_1(A_1, B_3) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.30/1.31  tff(c_416, plain, (![B_3]: (k11_relat_1(k1_xboole_0, B_3)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_410, c_2])).
% 2.30/1.31  tff(c_425, plain, (![B_3]: (k11_relat_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_213, c_416])).
% 2.30/1.31  tff(c_437, plain, (![B_68, A_69]: (k11_relat_1(B_68, A_69)!=k1_xboole_0 | ~r2_hidden(A_69, k1_relat_1(B_68)) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.30/1.31  tff(c_443, plain, (![A_24, A_69]: (k11_relat_1('#skF_2'(A_24), A_69)!=k1_xboole_0 | ~r2_hidden(A_69, A_24) | ~v1_relat_1('#skF_2'(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_437])).
% 2.30/1.31  tff(c_460, plain, (![A_72, A_73]: (k11_relat_1('#skF_2'(A_72), A_73)!=k1_xboole_0 | ~r2_hidden(A_73, A_72))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_443])).
% 2.30/1.31  tff(c_466, plain, (![A_73, A_24]: (k11_relat_1(k1_xboole_0, A_73)!=k1_xboole_0 | ~r2_hidden(A_73, A_24) | k1_xboole_0!=A_24)), inference(superposition, [status(thm), theory('equality')], [c_127, c_460])).
% 2.30/1.31  tff(c_469, plain, (![A_73, A_24]: (~r2_hidden(A_73, A_24) | k1_xboole_0!=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_425, c_466])).
% 2.30/1.31  tff(c_568, plain, (![A_88, A_89]: (k1_xboole_0!=A_88 | v5_funct_1('#skF_2'(A_88), A_89) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89))), inference(resolution, [status(thm)], [c_541, c_469])).
% 2.30/1.31  tff(c_571, plain, (![A_24, A_89]: (k1_xboole_0!=A_24 | v5_funct_1(k1_xboole_0, A_89) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89) | k1_xboole_0!=A_24)), inference(superposition, [status(thm), theory('equality')], [c_127, c_568])).
% 2.30/1.31  tff(c_572, plain, (![A_24]: (k1_xboole_0!=A_24 | k1_xboole_0!=A_24)), inference(splitLeft, [status(thm)], [c_571])).
% 2.30/1.31  tff(c_578, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_572])).
% 2.30/1.31  tff(c_601, plain, (![A_93]: (v5_funct_1(k1_xboole_0, A_93) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(splitRight, [status(thm)], [c_571])).
% 2.30/1.31  tff(c_42, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.30/1.31  tff(c_604, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_601, c_42])).
% 2.30/1.31  tff(c_608, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_604])).
% 2.30/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.31  
% 2.30/1.31  Inference rules
% 2.30/1.31  ----------------------
% 2.30/1.31  #Ref     : 2
% 2.30/1.31  #Sup     : 118
% 2.30/1.31  #Fact    : 0
% 2.30/1.31  #Define  : 0
% 2.30/1.31  #Split   : 5
% 2.30/1.31  #Chain   : 0
% 2.30/1.31  #Close   : 0
% 2.30/1.31  
% 2.30/1.31  Ordering : KBO
% 2.30/1.31  
% 2.30/1.31  Simplification rules
% 2.30/1.31  ----------------------
% 2.30/1.31  #Subsume      : 18
% 2.30/1.31  #Demod        : 40
% 2.30/1.31  #Tautology    : 65
% 2.30/1.31  #SimpNegUnit  : 26
% 2.30/1.31  #BackRed      : 16
% 2.30/1.31  
% 2.30/1.31  #Partial instantiations: 0
% 2.30/1.31  #Strategies tried      : 1
% 2.30/1.31  
% 2.30/1.31  Timing (in seconds)
% 2.30/1.31  ----------------------
% 2.30/1.31  Preprocessing        : 0.29
% 2.30/1.31  Parsing              : 0.17
% 2.30/1.31  CNF conversion       : 0.02
% 2.30/1.31  Main loop            : 0.29
% 2.30/1.31  Inferencing          : 0.11
% 2.30/1.31  Reduction            : 0.09
% 2.30/1.32  Demodulation         : 0.06
% 2.30/1.32  BG Simplification    : 0.02
% 2.30/1.32  Subsumption          : 0.05
% 2.30/1.32  Abstraction          : 0.01
% 2.30/1.32  MUC search           : 0.00
% 2.30/1.32  Cooper               : 0.00
% 2.30/1.32  Total                : 0.61
% 2.30/1.32  Index Insertion      : 0.00
% 2.30/1.32  Index Deletion       : 0.00
% 2.30/1.32  Index Matching       : 0.00
% 2.30/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
