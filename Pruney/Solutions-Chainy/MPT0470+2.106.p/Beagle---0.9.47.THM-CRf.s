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
% DateTime   : Thu Dec  3 09:59:15 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 113 expanded)
%              Number of leaves         :   31 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  129 ( 194 expanded)
%              Number of equality atoms :   32 (  60 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_96,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_42,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_84,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_93,plain,(
    ! [A_45] :
      ( r2_hidden('#skF_1'(A_45),A_45)
      | v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_85,plain,(
    ! [A_42,B_43] : ~ r2_hidden(A_42,k2_zfmisc_1(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_91,plain,(
    ! [A_5] : ~ r2_hidden(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_85])).

tff(c_98,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_93,c_91])).

tff(c_28,plain,(
    ! [A_27,B_28] :
      ( v1_relat_1(k5_relat_1(A_27,B_28))
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_166,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_61,B_62)),k1_relat_1(A_61))
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_171,plain,(
    ! [B_62] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_62)),k1_xboole_0)
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_166])).

tff(c_201,plain,(
    ! [B_64] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_64)),k1_xboole_0)
      | ~ v1_relat_1(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_171])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_112,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_121,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_112])).

tff(c_221,plain,(
    ! [B_67] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_67)) = k1_xboole_0
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_201,c_121])).

tff(c_30,plain,(
    ! [A_29] :
      ( ~ v1_xboole_0(k1_relat_1(A_29))
      | ~ v1_relat_1(A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_236,plain,(
    ! [B_67] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_67))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_67))
      | ~ v1_relat_1(B_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_30])).

tff(c_257,plain,(
    ! [B_73] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_73))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_73))
      | ~ v1_relat_1(B_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_236])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_283,plain,(
    ! [B_77] :
      ( k5_relat_1(k1_xboole_0,B_77) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_77))
      | ~ v1_relat_1(B_77) ) ),
    inference(resolution,[status(thm)],[c_257,c_4])).

tff(c_287,plain,(
    ! [B_28] :
      ( k5_relat_1(k1_xboole_0,B_28) = k1_xboole_0
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_283])).

tff(c_291,plain,(
    ! [B_78] :
      ( k5_relat_1(k1_xboole_0,B_78) = k1_xboole_0
      | ~ v1_relat_1(B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_287])).

tff(c_300,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_291])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_300])).

tff(c_307,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_321,plain,(
    ! [A_82] :
      ( r2_hidden('#skF_1'(A_82),A_82)
      | v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_313,plain,(
    ! [A_79,B_80] : ~ r2_hidden(A_79,k2_zfmisc_1(A_79,B_80)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_319,plain,(
    ! [A_5] : ~ r2_hidden(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_313])).

tff(c_326,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_321,c_319])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_380,plain,(
    ! [A_95,B_96] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_95,B_96)),k2_relat_1(B_96))
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_388,plain,(
    ! [A_95] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_95,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_380])).

tff(c_394,plain,(
    ! [A_97] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_97,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_388])).

tff(c_340,plain,(
    ! [B_88,A_89] :
      ( B_88 = A_89
      | ~ r1_tarski(B_88,A_89)
      | ~ r1_tarski(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_349,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_340])).

tff(c_418,plain,(
    ! [A_100] :
      ( k2_relat_1(k5_relat_1(A_100,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_100) ) ),
    inference(resolution,[status(thm)],[c_394,c_349])).

tff(c_32,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(k2_relat_1(A_30))
      | ~ v1_relat_1(A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_433,plain,(
    ! [A_100] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_100,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_100,k1_xboole_0))
      | ~ v1_relat_1(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_32])).

tff(c_541,plain,(
    ! [A_113] :
      ( ~ v1_relat_1(k5_relat_1(A_113,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_113,k1_xboole_0))
      | ~ v1_relat_1(A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_433])).

tff(c_573,plain,(
    ! [A_116] :
      ( k5_relat_1(A_116,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_116,k1_xboole_0))
      | ~ v1_relat_1(A_116) ) ),
    inference(resolution,[status(thm)],[c_541,c_4])).

tff(c_577,plain,(
    ! [A_27] :
      ( k5_relat_1(A_27,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_27) ) ),
    inference(resolution,[status(thm)],[c_28,c_573])).

tff(c_640,plain,(
    ! [A_117] :
      ( k5_relat_1(A_117,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_577])).

tff(c_649,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_640])).

tff(c_656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_649])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:23:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.37  
% 2.68/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.37  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.68/1.37  
% 2.68/1.37  %Foreground sorts:
% 2.68/1.37  
% 2.68/1.37  
% 2.68/1.37  %Background operators:
% 2.68/1.37  
% 2.68/1.37  
% 2.68/1.37  %Foreground operators:
% 2.68/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.68/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.68/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.68/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.68/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.68/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.68/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.68/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.68/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.68/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.68/1.37  
% 2.85/1.39  tff(f_103, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.85/1.39  tff(f_57, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.85/1.39  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.85/1.39  tff(f_47, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.85/1.39  tff(f_63, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.85/1.39  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.85/1.39  tff(f_96, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.85/1.39  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 2.85/1.39  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.85/1.39  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.85/1.39  tff(f_71, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.85/1.39  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.85/1.39  tff(f_93, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.85/1.39  tff(f_79, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.85/1.39  tff(c_42, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.85/1.39  tff(c_84, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 2.85/1.39  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.85/1.39  tff(c_93, plain, (![A_45]: (r2_hidden('#skF_1'(A_45), A_45) | v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.85/1.39  tff(c_16, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.85/1.39  tff(c_85, plain, (![A_42, B_43]: (~r2_hidden(A_42, k2_zfmisc_1(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.85/1.39  tff(c_91, plain, (![A_5]: (~r2_hidden(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_85])).
% 2.85/1.39  tff(c_98, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_93, c_91])).
% 2.85/1.39  tff(c_28, plain, (![A_27, B_28]: (v1_relat_1(k5_relat_1(A_27, B_28)) | ~v1_relat_1(B_28) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.85/1.39  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.85/1.39  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.85/1.39  tff(c_166, plain, (![A_61, B_62]: (r1_tarski(k1_relat_1(k5_relat_1(A_61, B_62)), k1_relat_1(A_61)) | ~v1_relat_1(B_62) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.85/1.39  tff(c_171, plain, (![B_62]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_62)), k1_xboole_0) | ~v1_relat_1(B_62) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_166])).
% 2.85/1.39  tff(c_201, plain, (![B_64]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_64)), k1_xboole_0) | ~v1_relat_1(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_171])).
% 2.85/1.39  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.85/1.39  tff(c_112, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.85/1.39  tff(c_121, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_112])).
% 2.85/1.39  tff(c_221, plain, (![B_67]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_67))=k1_xboole_0 | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_201, c_121])).
% 2.85/1.39  tff(c_30, plain, (![A_29]: (~v1_xboole_0(k1_relat_1(A_29)) | ~v1_relat_1(A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.85/1.39  tff(c_236, plain, (![B_67]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_67)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_67)) | ~v1_relat_1(B_67))), inference(superposition, [status(thm), theory('equality')], [c_221, c_30])).
% 2.85/1.39  tff(c_257, plain, (![B_73]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_73)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_73)) | ~v1_relat_1(B_73))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_236])).
% 2.85/1.39  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.85/1.39  tff(c_283, plain, (![B_77]: (k5_relat_1(k1_xboole_0, B_77)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_77)) | ~v1_relat_1(B_77))), inference(resolution, [status(thm)], [c_257, c_4])).
% 2.85/1.39  tff(c_287, plain, (![B_28]: (k5_relat_1(k1_xboole_0, B_28)=k1_xboole_0 | ~v1_relat_1(B_28) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_283])).
% 2.85/1.39  tff(c_291, plain, (![B_78]: (k5_relat_1(k1_xboole_0, B_78)=k1_xboole_0 | ~v1_relat_1(B_78))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_287])).
% 2.85/1.39  tff(c_300, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_291])).
% 2.85/1.39  tff(c_306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_300])).
% 2.85/1.39  tff(c_307, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 2.85/1.39  tff(c_321, plain, (![A_82]: (r2_hidden('#skF_1'(A_82), A_82) | v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.85/1.39  tff(c_313, plain, (![A_79, B_80]: (~r2_hidden(A_79, k2_zfmisc_1(A_79, B_80)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.85/1.39  tff(c_319, plain, (![A_5]: (~r2_hidden(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_313])).
% 2.85/1.39  tff(c_326, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_321, c_319])).
% 2.85/1.39  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.85/1.39  tff(c_380, plain, (![A_95, B_96]: (r1_tarski(k2_relat_1(k5_relat_1(A_95, B_96)), k2_relat_1(B_96)) | ~v1_relat_1(B_96) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.85/1.39  tff(c_388, plain, (![A_95]: (r1_tarski(k2_relat_1(k5_relat_1(A_95, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_95))), inference(superposition, [status(thm), theory('equality')], [c_38, c_380])).
% 2.85/1.39  tff(c_394, plain, (![A_97]: (r1_tarski(k2_relat_1(k5_relat_1(A_97, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_97))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_388])).
% 2.85/1.39  tff(c_340, plain, (![B_88, A_89]: (B_88=A_89 | ~r1_tarski(B_88, A_89) | ~r1_tarski(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.85/1.39  tff(c_349, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_340])).
% 2.85/1.39  tff(c_418, plain, (![A_100]: (k2_relat_1(k5_relat_1(A_100, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_100))), inference(resolution, [status(thm)], [c_394, c_349])).
% 2.85/1.39  tff(c_32, plain, (![A_30]: (~v1_xboole_0(k2_relat_1(A_30)) | ~v1_relat_1(A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.85/1.39  tff(c_433, plain, (![A_100]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_100, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_100, k1_xboole_0)) | ~v1_relat_1(A_100))), inference(superposition, [status(thm), theory('equality')], [c_418, c_32])).
% 2.85/1.39  tff(c_541, plain, (![A_113]: (~v1_relat_1(k5_relat_1(A_113, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_113, k1_xboole_0)) | ~v1_relat_1(A_113))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_433])).
% 2.85/1.39  tff(c_573, plain, (![A_116]: (k5_relat_1(A_116, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_116, k1_xboole_0)) | ~v1_relat_1(A_116))), inference(resolution, [status(thm)], [c_541, c_4])).
% 2.85/1.39  tff(c_577, plain, (![A_27]: (k5_relat_1(A_27, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_27))), inference(resolution, [status(thm)], [c_28, c_573])).
% 2.85/1.39  tff(c_640, plain, (![A_117]: (k5_relat_1(A_117, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_117))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_577])).
% 2.85/1.39  tff(c_649, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_640])).
% 2.85/1.39  tff(c_656, plain, $false, inference(negUnitSimplification, [status(thm)], [c_307, c_649])).
% 2.85/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.39  
% 2.85/1.39  Inference rules
% 2.85/1.39  ----------------------
% 2.85/1.39  #Ref     : 2
% 2.85/1.39  #Sup     : 126
% 2.85/1.39  #Fact    : 0
% 2.85/1.39  #Define  : 0
% 2.85/1.39  #Split   : 1
% 2.85/1.39  #Chain   : 0
% 2.85/1.39  #Close   : 0
% 2.85/1.39  
% 2.85/1.39  Ordering : KBO
% 2.85/1.39  
% 2.85/1.39  Simplification rules
% 2.85/1.39  ----------------------
% 2.85/1.39  #Subsume      : 13
% 2.85/1.39  #Demod        : 134
% 2.85/1.39  #Tautology    : 73
% 2.85/1.39  #SimpNegUnit  : 2
% 2.85/1.39  #BackRed      : 0
% 2.85/1.39  
% 2.85/1.39  #Partial instantiations: 0
% 2.85/1.39  #Strategies tried      : 1
% 2.85/1.39  
% 2.85/1.39  Timing (in seconds)
% 2.85/1.39  ----------------------
% 2.85/1.39  Preprocessing        : 0.31
% 2.85/1.39  Parsing              : 0.17
% 2.85/1.39  CNF conversion       : 0.02
% 2.85/1.39  Main loop            : 0.31
% 2.85/1.39  Inferencing          : 0.12
% 2.85/1.39  Reduction            : 0.09
% 2.85/1.39  Demodulation         : 0.06
% 2.85/1.39  BG Simplification    : 0.02
% 2.85/1.39  Subsumption          : 0.05
% 2.85/1.39  Abstraction          : 0.01
% 2.85/1.39  MUC search           : 0.00
% 2.85/1.39  Cooper               : 0.00
% 2.85/1.39  Total                : 0.65
% 2.85/1.39  Index Insertion      : 0.00
% 2.85/1.39  Index Deletion       : 0.00
% 2.85/1.39  Index Matching       : 0.00
% 2.85/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
