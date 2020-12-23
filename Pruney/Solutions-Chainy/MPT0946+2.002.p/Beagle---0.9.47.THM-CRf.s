%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:31 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 420 expanded)
%              Number of leaves         :   34 ( 163 expanded)
%              Depth                    :   15
%              Number of atoms          :  191 (1143 expanded)
%              Number of equality atoms :   27 ( 166 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v2_ordinal1 > v1_relat_1 > v1_ordinal1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_123,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_110,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_127,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_108,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_119,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_44,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_74,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_xboole_0(A,B)
              & A != B
              & ~ r2_xboole_0(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_ordinal1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_54,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_60,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_50,plain,(
    ! [A_32] :
      ( v2_wellord1(k1_wellord2(A_32))
      | ~ v3_ordinal1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_58,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_46,plain,(
    ! [A_28] : v1_relat_1(k1_wellord2(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_56,plain,(
    r4_wellord1(k1_wellord2('#skF_3'),k1_wellord2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_135,plain,(
    ! [B_55,A_56] :
      ( r4_wellord1(B_55,A_56)
      | ~ r4_wellord1(A_56,B_55)
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_137,plain,
    ( r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3'))
    | ~ v1_relat_1(k1_wellord2('#skF_4'))
    | ~ v1_relat_1(k1_wellord2('#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_135])).

tff(c_140,plain,(
    r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_137])).

tff(c_52,plain,(
    ! [B_34,A_33] :
      ( k2_wellord1(k1_wellord2(B_34),A_33) = k1_wellord2(A_33)
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_40,plain,(
    ! [A_20] :
      ( k3_relat_1(k1_wellord2(A_20)) = A_20
      | ~ v1_relat_1(k1_wellord2(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_66,plain,(
    ! [A_20] : k3_relat_1(k1_wellord2(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40])).

tff(c_48,plain,(
    ! [B_31,A_29] :
      ( k1_wellord1(k1_wellord2(B_31),A_29) = A_29
      | ~ r2_hidden(A_29,B_31)
      | ~ v3_ordinal1(B_31)
      | ~ v3_ordinal1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_349,plain,(
    ! [A_81,B_82] :
      ( ~ r4_wellord1(A_81,k2_wellord1(A_81,k1_wellord1(A_81,B_82)))
      | ~ r2_hidden(B_82,k3_relat_1(A_81))
      | ~ v2_wellord1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_352,plain,(
    ! [B_31,A_29] :
      ( ~ r4_wellord1(k1_wellord2(B_31),k2_wellord1(k1_wellord2(B_31),A_29))
      | ~ r2_hidden(A_29,k3_relat_1(k1_wellord2(B_31)))
      | ~ v2_wellord1(k1_wellord2(B_31))
      | ~ v1_relat_1(k1_wellord2(B_31))
      | ~ r2_hidden(A_29,B_31)
      | ~ v3_ordinal1(B_31)
      | ~ v3_ordinal1(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_349])).

tff(c_444,plain,(
    ! [B_95,A_96] :
      ( ~ r4_wellord1(k1_wellord2(B_95),k2_wellord1(k1_wellord2(B_95),A_96))
      | ~ v2_wellord1(k1_wellord2(B_95))
      | ~ r2_hidden(A_96,B_95)
      | ~ v3_ordinal1(B_95)
      | ~ v3_ordinal1(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_66,c_352])).

tff(c_490,plain,(
    ! [B_98,A_99] :
      ( ~ r4_wellord1(k1_wellord2(B_98),k1_wellord2(A_99))
      | ~ v2_wellord1(k1_wellord2(B_98))
      | ~ r2_hidden(A_99,B_98)
      | ~ v3_ordinal1(B_98)
      | ~ v3_ordinal1(A_99)
      | ~ r1_tarski(A_99,B_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_444])).

tff(c_493,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_140,c_490])).

tff(c_499,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_493])).

tff(c_503,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_499])).

tff(c_80,plain,(
    ! [A_40] :
      ( v1_ordinal1(A_40)
      | ~ v3_ordinal1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_87,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_80])).

tff(c_175,plain,(
    ! [B_59,A_60] :
      ( r2_xboole_0(B_59,A_60)
      | B_59 = A_60
      | r2_xboole_0(A_60,B_59)
      | ~ v3_ordinal1(B_59)
      | ~ v3_ordinal1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    ! [A_6,B_8] :
      ( r2_hidden(A_6,B_8)
      | ~ r2_xboole_0(A_6,B_8)
      | ~ v3_ordinal1(B_8)
      | ~ v1_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_300,plain,(
    ! [A_72,B_73] :
      ( r2_hidden(A_72,B_73)
      | ~ v1_ordinal1(A_72)
      | r2_xboole_0(B_73,A_72)
      | B_73 = A_72
      | ~ v3_ordinal1(B_73)
      | ~ v3_ordinal1(A_72) ) ),
    inference(resolution,[status(thm)],[c_175,c_18])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_312,plain,(
    ! [B_73,A_72] :
      ( r1_tarski(B_73,A_72)
      | r2_hidden(A_72,B_73)
      | ~ v1_ordinal1(A_72)
      | B_73 = A_72
      | ~ v3_ordinal1(B_73)
      | ~ v3_ordinal1(A_72) ) ),
    inference(resolution,[status(thm)],[c_300,c_6])).

tff(c_222,plain,(
    ! [B_66,A_67] :
      ( r1_tarski(B_66,A_67)
      | B_66 = A_67
      | r2_xboole_0(A_67,B_66)
      | ~ v3_ordinal1(B_66)
      | ~ v3_ordinal1(A_67) ) ),
    inference(resolution,[status(thm)],[c_175,c_6])).

tff(c_234,plain,(
    ! [A_67,B_66] :
      ( r1_tarski(A_67,B_66)
      | r1_tarski(B_66,A_67)
      | B_66 = A_67
      | ~ v3_ordinal1(B_66)
      | ~ v3_ordinal1(A_67) ) ),
    inference(resolution,[status(thm)],[c_222,c_6])).

tff(c_506,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_234,c_503])).

tff(c_512,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_506])).

tff(c_513,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_512])).

tff(c_496,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_490])).

tff(c_502,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_496])).

tff(c_535,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_502])).

tff(c_536,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_535])).

tff(c_541,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ v1_ordinal1('#skF_4')
    | '#skF_3' = '#skF_4'
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_312,c_536])).

tff(c_547,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_87,c_541])).

tff(c_549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_503,c_547])).

tff(c_550,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_535])).

tff(c_554,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_550])).

tff(c_558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_554])).

tff(c_560,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_499])).

tff(c_561,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_502])).

tff(c_88,plain,(
    v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_80])).

tff(c_559,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_499])).

tff(c_576,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_559])).

tff(c_579,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_576])).

tff(c_583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_579])).

tff(c_584,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_559])).

tff(c_598,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ v1_ordinal1('#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_312,c_584])).

tff(c_612,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_88,c_598])).

tff(c_614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_561,c_612])).

tff(c_616,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_502])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_633,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_616,c_8])).

tff(c_640,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_633])).

tff(c_642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_640])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:03:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.43  
% 2.71/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.43  %$ r4_wellord1 > r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v2_ordinal1 > v1_relat_1 > v1_ordinal1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.71/1.43  
% 2.71/1.43  %Foreground sorts:
% 2.71/1.43  
% 2.71/1.43  
% 2.71/1.43  %Background operators:
% 2.71/1.43  
% 2.71/1.43  
% 2.71/1.43  %Foreground operators:
% 2.71/1.43  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 2.71/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.43  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.71/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.71/1.43  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.71/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.43  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.71/1.43  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.71/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.43  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.71/1.43  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.71/1.43  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.71/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.71/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.43  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.71/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.71/1.43  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.71/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.71/1.43  
% 2.71/1.45  tff(f_137, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord2)).
% 2.71/1.45  tff(f_123, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 2.71/1.45  tff(f_110, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.71/1.45  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 2.71/1.45  tff(f_127, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 2.71/1.45  tff(f_108, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 2.71/1.45  tff(f_119, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord2)).
% 2.71/1.45  tff(f_93, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_wellord1)).
% 2.71/1.45  tff(f_44, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 2.71/1.45  tff(f_74, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_xboole_0(A, B) & ~(A = B)) & ~r2_xboole_0(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_ordinal1)).
% 2.71/1.45  tff(f_53, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 2.71/1.45  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.71/1.45  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.71/1.45  tff(c_54, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.71/1.45  tff(c_60, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.71/1.45  tff(c_50, plain, (![A_32]: (v2_wellord1(k1_wellord2(A_32)) | ~v3_ordinal1(A_32))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.71/1.45  tff(c_58, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.71/1.45  tff(c_46, plain, (![A_28]: (v1_relat_1(k1_wellord2(A_28)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.71/1.45  tff(c_56, plain, (r4_wellord1(k1_wellord2('#skF_3'), k1_wellord2('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.71/1.45  tff(c_135, plain, (![B_55, A_56]: (r4_wellord1(B_55, A_56) | ~r4_wellord1(A_56, B_55) | ~v1_relat_1(B_55) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.71/1.45  tff(c_137, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3')) | ~v1_relat_1(k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_135])).
% 2.71/1.45  tff(c_140, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_137])).
% 2.71/1.45  tff(c_52, plain, (![B_34, A_33]: (k2_wellord1(k1_wellord2(B_34), A_33)=k1_wellord2(A_33) | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.71/1.45  tff(c_40, plain, (![A_20]: (k3_relat_1(k1_wellord2(A_20))=A_20 | ~v1_relat_1(k1_wellord2(A_20)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.71/1.45  tff(c_66, plain, (![A_20]: (k3_relat_1(k1_wellord2(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40])).
% 2.71/1.45  tff(c_48, plain, (![B_31, A_29]: (k1_wellord1(k1_wellord2(B_31), A_29)=A_29 | ~r2_hidden(A_29, B_31) | ~v3_ordinal1(B_31) | ~v3_ordinal1(A_29))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.71/1.45  tff(c_349, plain, (![A_81, B_82]: (~r4_wellord1(A_81, k2_wellord1(A_81, k1_wellord1(A_81, B_82))) | ~r2_hidden(B_82, k3_relat_1(A_81)) | ~v2_wellord1(A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.71/1.45  tff(c_352, plain, (![B_31, A_29]: (~r4_wellord1(k1_wellord2(B_31), k2_wellord1(k1_wellord2(B_31), A_29)) | ~r2_hidden(A_29, k3_relat_1(k1_wellord2(B_31))) | ~v2_wellord1(k1_wellord2(B_31)) | ~v1_relat_1(k1_wellord2(B_31)) | ~r2_hidden(A_29, B_31) | ~v3_ordinal1(B_31) | ~v3_ordinal1(A_29))), inference(superposition, [status(thm), theory('equality')], [c_48, c_349])).
% 2.71/1.45  tff(c_444, plain, (![B_95, A_96]: (~r4_wellord1(k1_wellord2(B_95), k2_wellord1(k1_wellord2(B_95), A_96)) | ~v2_wellord1(k1_wellord2(B_95)) | ~r2_hidden(A_96, B_95) | ~v3_ordinal1(B_95) | ~v3_ordinal1(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_66, c_352])).
% 2.71/1.45  tff(c_490, plain, (![B_98, A_99]: (~r4_wellord1(k1_wellord2(B_98), k1_wellord2(A_99)) | ~v2_wellord1(k1_wellord2(B_98)) | ~r2_hidden(A_99, B_98) | ~v3_ordinal1(B_98) | ~v3_ordinal1(A_99) | ~r1_tarski(A_99, B_98))), inference(superposition, [status(thm), theory('equality')], [c_52, c_444])).
% 2.71/1.45  tff(c_493, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3') | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_140, c_490])).
% 2.71/1.45  tff(c_499, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_493])).
% 2.71/1.45  tff(c_503, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_499])).
% 2.71/1.45  tff(c_80, plain, (![A_40]: (v1_ordinal1(A_40) | ~v3_ordinal1(A_40))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.71/1.45  tff(c_87, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_80])).
% 2.71/1.45  tff(c_175, plain, (![B_59, A_60]: (r2_xboole_0(B_59, A_60) | B_59=A_60 | r2_xboole_0(A_60, B_59) | ~v3_ordinal1(B_59) | ~v3_ordinal1(A_60))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.71/1.45  tff(c_18, plain, (![A_6, B_8]: (r2_hidden(A_6, B_8) | ~r2_xboole_0(A_6, B_8) | ~v3_ordinal1(B_8) | ~v1_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.71/1.45  tff(c_300, plain, (![A_72, B_73]: (r2_hidden(A_72, B_73) | ~v1_ordinal1(A_72) | r2_xboole_0(B_73, A_72) | B_73=A_72 | ~v3_ordinal1(B_73) | ~v3_ordinal1(A_72))), inference(resolution, [status(thm)], [c_175, c_18])).
% 2.71/1.45  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.45  tff(c_312, plain, (![B_73, A_72]: (r1_tarski(B_73, A_72) | r2_hidden(A_72, B_73) | ~v1_ordinal1(A_72) | B_73=A_72 | ~v3_ordinal1(B_73) | ~v3_ordinal1(A_72))), inference(resolution, [status(thm)], [c_300, c_6])).
% 2.71/1.45  tff(c_222, plain, (![B_66, A_67]: (r1_tarski(B_66, A_67) | B_66=A_67 | r2_xboole_0(A_67, B_66) | ~v3_ordinal1(B_66) | ~v3_ordinal1(A_67))), inference(resolution, [status(thm)], [c_175, c_6])).
% 2.71/1.45  tff(c_234, plain, (![A_67, B_66]: (r1_tarski(A_67, B_66) | r1_tarski(B_66, A_67) | B_66=A_67 | ~v3_ordinal1(B_66) | ~v3_ordinal1(A_67))), inference(resolution, [status(thm)], [c_222, c_6])).
% 2.71/1.45  tff(c_506, plain, (r1_tarski('#skF_4', '#skF_3') | '#skF_3'='#skF_4' | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_234, c_503])).
% 2.71/1.45  tff(c_512, plain, (r1_tarski('#skF_4', '#skF_3') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_506])).
% 2.71/1.45  tff(c_513, plain, (r1_tarski('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_512])).
% 2.71/1.45  tff(c_496, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_490])).
% 2.71/1.45  tff(c_502, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_496])).
% 2.71/1.45  tff(c_535, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_513, c_502])).
% 2.71/1.45  tff(c_536, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_535])).
% 2.71/1.45  tff(c_541, plain, (r1_tarski('#skF_3', '#skF_4') | ~v1_ordinal1('#skF_4') | '#skF_3'='#skF_4' | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_312, c_536])).
% 2.71/1.45  tff(c_547, plain, (r1_tarski('#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_87, c_541])).
% 2.71/1.45  tff(c_549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_503, c_547])).
% 2.71/1.45  tff(c_550, plain, (~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitRight, [status(thm)], [c_535])).
% 2.71/1.45  tff(c_554, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_550])).
% 2.71/1.45  tff(c_558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_554])).
% 2.71/1.45  tff(c_560, plain, (r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_499])).
% 2.71/1.45  tff(c_561, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_502])).
% 2.71/1.45  tff(c_88, plain, (v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_80])).
% 2.71/1.45  tff(c_559, plain, (~r2_hidden('#skF_3', '#skF_4') | ~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitRight, [status(thm)], [c_499])).
% 2.71/1.45  tff(c_576, plain, (~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitLeft, [status(thm)], [c_559])).
% 2.71/1.45  tff(c_579, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_576])).
% 2.71/1.45  tff(c_583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_579])).
% 2.71/1.45  tff(c_584, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_559])).
% 2.71/1.45  tff(c_598, plain, (r1_tarski('#skF_4', '#skF_3') | ~v1_ordinal1('#skF_3') | '#skF_3'='#skF_4' | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_312, c_584])).
% 2.71/1.45  tff(c_612, plain, (r1_tarski('#skF_4', '#skF_3') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_88, c_598])).
% 2.71/1.45  tff(c_614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_561, c_612])).
% 2.71/1.45  tff(c_616, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_502])).
% 2.71/1.45  tff(c_8, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.71/1.45  tff(c_633, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_616, c_8])).
% 2.71/1.45  tff(c_640, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_560, c_633])).
% 2.71/1.45  tff(c_642, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_640])).
% 2.71/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.45  
% 2.71/1.45  Inference rules
% 2.71/1.45  ----------------------
% 2.71/1.45  #Ref     : 0
% 2.71/1.45  #Sup     : 94
% 2.71/1.45  #Fact    : 6
% 2.71/1.45  #Define  : 0
% 2.71/1.45  #Split   : 4
% 2.71/1.45  #Chain   : 0
% 2.71/1.45  #Close   : 0
% 2.71/1.45  
% 2.71/1.45  Ordering : KBO
% 2.71/1.45  
% 2.71/1.45  Simplification rules
% 2.71/1.45  ----------------------
% 2.71/1.45  #Subsume      : 5
% 2.71/1.45  #Demod        : 119
% 2.71/1.45  #Tautology    : 52
% 2.71/1.45  #SimpNegUnit  : 16
% 2.71/1.45  #BackRed      : 0
% 2.71/1.45  
% 2.71/1.45  #Partial instantiations: 0
% 2.71/1.45  #Strategies tried      : 1
% 2.71/1.45  
% 2.71/1.45  Timing (in seconds)
% 2.71/1.45  ----------------------
% 2.71/1.45  Preprocessing        : 0.34
% 2.71/1.45  Parsing              : 0.17
% 2.71/1.45  CNF conversion       : 0.03
% 2.71/1.45  Main loop            : 0.33
% 2.71/1.45  Inferencing          : 0.12
% 2.71/1.46  Reduction            : 0.10
% 2.71/1.46  Demodulation         : 0.07
% 2.71/1.46  BG Simplification    : 0.02
% 2.71/1.46  Subsumption          : 0.07
% 2.71/1.46  Abstraction          : 0.01
% 2.71/1.46  MUC search           : 0.00
% 2.71/1.46  Cooper               : 0.00
% 2.71/1.46  Total                : 0.70
% 2.71/1.46  Index Insertion      : 0.00
% 2.71/1.46  Index Deletion       : 0.00
% 2.71/1.46  Index Matching       : 0.00
% 2.71/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
