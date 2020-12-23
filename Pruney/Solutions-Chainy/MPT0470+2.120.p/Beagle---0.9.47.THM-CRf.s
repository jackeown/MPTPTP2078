%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:17 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 128 expanded)
%              Number of leaves         :   41 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  117 ( 192 expanded)
%              Number of equality atoms :   39 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_36,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_32,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_102,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_48,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_83,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_34,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_1'(A_28),A_28)
      | v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_105,plain,(
    ! [A_67,B_68] :
      ( ~ r2_hidden(A_67,B_68)
      | ~ r1_xboole_0(k1_tarski(A_67),B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_111,plain,(
    ! [A_69] : ~ r2_hidden(A_69,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_105])).

tff(c_116,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_111])).

tff(c_36,plain,(
    ! [A_46,B_47] :
      ( v1_relat_1(k5_relat_1(A_46,B_47))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [A_2] : k3_xboole_0(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_85,plain,(
    ! [A_61,B_62] :
      ( v1_xboole_0(k2_zfmisc_1(A_61,B_62))
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_95,plain,(
    ! [A_65,B_66] :
      ( k2_zfmisc_1(A_65,B_66) = k1_xboole_0
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_85,c_4])).

tff(c_104,plain,(
    ! [B_66] : k2_zfmisc_1(k1_xboole_0,B_66) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_95])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_46,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_44,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_527,plain,(
    ! [A_111,B_112] :
      ( k1_relat_1(k5_relat_1(A_111,B_112)) = k1_relat_1(A_111)
      | ~ r1_tarski(k2_relat_1(A_111),k1_relat_1(B_112))
      | ~ v1_relat_1(B_112)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_533,plain,(
    ! [B_112] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_112)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_112))
      | ~ v1_relat_1(B_112)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_527])).

tff(c_538,plain,(
    ! [B_113] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_113)) = k1_xboole_0
      | ~ v1_relat_1(B_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_8,c_46,c_533])).

tff(c_38,plain,(
    ! [A_48] :
      ( k3_xboole_0(A_48,k2_zfmisc_1(k1_relat_1(A_48),k2_relat_1(A_48))) = A_48
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_547,plain,(
    ! [B_113] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_113),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_113)))) = k5_relat_1(k1_xboole_0,B_113)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_113))
      | ~ v1_relat_1(B_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_38])).

tff(c_601,plain,(
    ! [B_122] :
      ( k5_relat_1(k1_xboole_0,B_122) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_122))
      | ~ v1_relat_1(B_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_104,c_547])).

tff(c_605,plain,(
    ! [B_47] :
      ( k5_relat_1(k1_xboole_0,B_47) = k1_xboole_0
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36,c_601])).

tff(c_609,plain,(
    ! [B_123] :
      ( k5_relat_1(k1_xboole_0,B_123) = k1_xboole_0
      | ~ v1_relat_1(B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_605])).

tff(c_618,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_609])).

tff(c_624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_618])).

tff(c_625,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_731,plain,(
    ! [A_138,B_139] :
      ( ~ r2_hidden(A_138,B_139)
      | ~ r1_xboole_0(k1_tarski(A_138),B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_746,plain,(
    ! [A_142] : ~ r2_hidden(A_142,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_731])).

tff(c_751,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_746])).

tff(c_632,plain,(
    ! [A_125,B_126] :
      ( v1_xboole_0(k2_zfmisc_1(A_125,B_126))
      | ~ v1_xboole_0(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_642,plain,(
    ! [A_129,B_130] :
      ( k2_zfmisc_1(A_129,B_130) = k1_xboole_0
      | ~ v1_xboole_0(B_130) ) ),
    inference(resolution,[status(thm)],[c_632,c_4])).

tff(c_651,plain,(
    ! [A_129] : k2_zfmisc_1(A_129,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_642])).

tff(c_1148,plain,(
    ! [B_185,A_186] :
      ( k2_relat_1(k5_relat_1(B_185,A_186)) = k2_relat_1(A_186)
      | ~ r1_tarski(k1_relat_1(A_186),k2_relat_1(B_185))
      | ~ v1_relat_1(B_185)
      | ~ v1_relat_1(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1154,plain,(
    ! [B_185] :
      ( k2_relat_1(k5_relat_1(B_185,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_185))
      | ~ v1_relat_1(B_185)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1148])).

tff(c_1178,plain,(
    ! [B_187] :
      ( k2_relat_1(k5_relat_1(B_187,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_8,c_44,c_1154])).

tff(c_1190,plain,(
    ! [B_187] :
      ( k3_xboole_0(k5_relat_1(B_187,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_187,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_187,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_187,k1_xboole_0))
      | ~ v1_relat_1(B_187) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1178,c_38])).

tff(c_1204,plain,(
    ! [B_188] :
      ( k5_relat_1(B_188,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_188,k1_xboole_0))
      | ~ v1_relat_1(B_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_651,c_1190])).

tff(c_1211,plain,(
    ! [A_46] :
      ( k5_relat_1(A_46,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_36,c_1204])).

tff(c_1255,plain,(
    ! [A_191] :
      ( k5_relat_1(A_191,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_1211])).

tff(c_1264,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_1255])).

tff(c_1271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_625,c_1264])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:07:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.45  
% 3.01/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.45  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.01/1.45  
% 3.01/1.45  %Foreground sorts:
% 3.01/1.45  
% 3.01/1.45  
% 3.01/1.45  %Background operators:
% 3.01/1.45  
% 3.01/1.45  
% 3.01/1.45  %Foreground operators:
% 3.01/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.01/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.01/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.01/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.01/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.01/1.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.01/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.01/1.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.01/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.01/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.01/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.01/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.01/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.01/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.01/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.01/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.01/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.01/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.01/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.01/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.01/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.01/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.01/1.45  
% 3.01/1.47  tff(f_109, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.01/1.47  tff(f_71, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 3.01/1.47  tff(f_36, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.01/1.47  tff(f_59, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.01/1.47  tff(f_77, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.01/1.47  tff(f_32, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.01/1.47  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.01/1.47  tff(f_54, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 3.01/1.47  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.01/1.47  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.01/1.47  tff(f_102, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.01/1.47  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 3.01/1.47  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 3.01/1.47  tff(f_50, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.01/1.47  tff(f_99, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 3.01/1.47  tff(c_48, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.01/1.47  tff(c_83, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 3.01/1.47  tff(c_50, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.01/1.47  tff(c_34, plain, (![A_28]: (r2_hidden('#skF_1'(A_28), A_28) | v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.01/1.47  tff(c_10, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.01/1.47  tff(c_105, plain, (![A_67, B_68]: (~r2_hidden(A_67, B_68) | ~r1_xboole_0(k1_tarski(A_67), B_68))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.01/1.47  tff(c_111, plain, (![A_69]: (~r2_hidden(A_69, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_105])).
% 3.01/1.47  tff(c_116, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_111])).
% 3.01/1.47  tff(c_36, plain, (![A_46, B_47]: (v1_relat_1(k5_relat_1(A_46, B_47)) | ~v1_relat_1(B_47) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.01/1.47  tff(c_6, plain, (![A_2]: (k3_xboole_0(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.01/1.47  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.01/1.47  tff(c_85, plain, (![A_61, B_62]: (v1_xboole_0(k2_zfmisc_1(A_61, B_62)) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.01/1.47  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.01/1.47  tff(c_95, plain, (![A_65, B_66]: (k2_zfmisc_1(A_65, B_66)=k1_xboole_0 | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_85, c_4])).
% 3.01/1.47  tff(c_104, plain, (![B_66]: (k2_zfmisc_1(k1_xboole_0, B_66)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_95])).
% 3.01/1.47  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.01/1.47  tff(c_46, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.01/1.47  tff(c_44, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.01/1.47  tff(c_527, plain, (![A_111, B_112]: (k1_relat_1(k5_relat_1(A_111, B_112))=k1_relat_1(A_111) | ~r1_tarski(k2_relat_1(A_111), k1_relat_1(B_112)) | ~v1_relat_1(B_112) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.01/1.47  tff(c_533, plain, (![B_112]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_112))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_112)) | ~v1_relat_1(B_112) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_527])).
% 3.01/1.47  tff(c_538, plain, (![B_113]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_113))=k1_xboole_0 | ~v1_relat_1(B_113))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_8, c_46, c_533])).
% 3.01/1.47  tff(c_38, plain, (![A_48]: (k3_xboole_0(A_48, k2_zfmisc_1(k1_relat_1(A_48), k2_relat_1(A_48)))=A_48 | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.01/1.47  tff(c_547, plain, (![B_113]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_113), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_113))))=k5_relat_1(k1_xboole_0, B_113) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_113)) | ~v1_relat_1(B_113))), inference(superposition, [status(thm), theory('equality')], [c_538, c_38])).
% 3.01/1.47  tff(c_601, plain, (![B_122]: (k5_relat_1(k1_xboole_0, B_122)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_122)) | ~v1_relat_1(B_122))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_104, c_547])).
% 3.01/1.47  tff(c_605, plain, (![B_47]: (k5_relat_1(k1_xboole_0, B_47)=k1_xboole_0 | ~v1_relat_1(B_47) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_601])).
% 3.01/1.47  tff(c_609, plain, (![B_123]: (k5_relat_1(k1_xboole_0, B_123)=k1_xboole_0 | ~v1_relat_1(B_123))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_605])).
% 3.01/1.47  tff(c_618, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_609])).
% 3.01/1.47  tff(c_624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_618])).
% 3.01/1.47  tff(c_625, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 3.01/1.47  tff(c_731, plain, (![A_138, B_139]: (~r2_hidden(A_138, B_139) | ~r1_xboole_0(k1_tarski(A_138), B_139))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.01/1.47  tff(c_746, plain, (![A_142]: (~r2_hidden(A_142, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_731])).
% 3.01/1.47  tff(c_751, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_746])).
% 3.01/1.47  tff(c_632, plain, (![A_125, B_126]: (v1_xboole_0(k2_zfmisc_1(A_125, B_126)) | ~v1_xboole_0(B_126))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.01/1.47  tff(c_642, plain, (![A_129, B_130]: (k2_zfmisc_1(A_129, B_130)=k1_xboole_0 | ~v1_xboole_0(B_130))), inference(resolution, [status(thm)], [c_632, c_4])).
% 3.01/1.47  tff(c_651, plain, (![A_129]: (k2_zfmisc_1(A_129, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_642])).
% 3.01/1.47  tff(c_1148, plain, (![B_185, A_186]: (k2_relat_1(k5_relat_1(B_185, A_186))=k2_relat_1(A_186) | ~r1_tarski(k1_relat_1(A_186), k2_relat_1(B_185)) | ~v1_relat_1(B_185) | ~v1_relat_1(A_186))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.01/1.47  tff(c_1154, plain, (![B_185]: (k2_relat_1(k5_relat_1(B_185, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_185)) | ~v1_relat_1(B_185) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1148])).
% 3.01/1.47  tff(c_1178, plain, (![B_187]: (k2_relat_1(k5_relat_1(B_187, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_187))), inference(demodulation, [status(thm), theory('equality')], [c_751, c_8, c_44, c_1154])).
% 3.01/1.47  tff(c_1190, plain, (![B_187]: (k3_xboole_0(k5_relat_1(B_187, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_187, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_187, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_187, k1_xboole_0)) | ~v1_relat_1(B_187))), inference(superposition, [status(thm), theory('equality')], [c_1178, c_38])).
% 3.01/1.47  tff(c_1204, plain, (![B_188]: (k5_relat_1(B_188, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_188, k1_xboole_0)) | ~v1_relat_1(B_188))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_651, c_1190])).
% 3.01/1.47  tff(c_1211, plain, (![A_46]: (k5_relat_1(A_46, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_36, c_1204])).
% 3.01/1.47  tff(c_1255, plain, (![A_191]: (k5_relat_1(A_191, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_191))), inference(demodulation, [status(thm), theory('equality')], [c_751, c_1211])).
% 3.01/1.47  tff(c_1264, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_1255])).
% 3.01/1.47  tff(c_1271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_625, c_1264])).
% 3.01/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.47  
% 3.01/1.47  Inference rules
% 3.01/1.47  ----------------------
% 3.01/1.47  #Ref     : 2
% 3.01/1.47  #Sup     : 282
% 3.01/1.47  #Fact    : 0
% 3.01/1.47  #Define  : 0
% 3.01/1.47  #Split   : 1
% 3.01/1.47  #Chain   : 0
% 3.01/1.47  #Close   : 0
% 3.01/1.47  
% 3.01/1.47  Ordering : KBO
% 3.01/1.47  
% 3.01/1.47  Simplification rules
% 3.01/1.47  ----------------------
% 3.01/1.47  #Subsume      : 3
% 3.01/1.47  #Demod        : 172
% 3.01/1.47  #Tautology    : 228
% 3.01/1.47  #SimpNegUnit  : 2
% 3.01/1.47  #BackRed      : 0
% 3.01/1.47  
% 3.01/1.47  #Partial instantiations: 0
% 3.01/1.47  #Strategies tried      : 1
% 3.01/1.47  
% 3.01/1.47  Timing (in seconds)
% 3.01/1.47  ----------------------
% 3.01/1.47  Preprocessing        : 0.33
% 3.01/1.47  Parsing              : 0.18
% 3.01/1.47  CNF conversion       : 0.02
% 3.01/1.47  Main loop            : 0.37
% 3.01/1.47  Inferencing          : 0.15
% 3.01/1.47  Reduction            : 0.11
% 3.01/1.47  Demodulation         : 0.08
% 3.01/1.47  BG Simplification    : 0.02
% 3.01/1.47  Subsumption          : 0.06
% 3.01/1.47  Abstraction          : 0.02
% 3.01/1.47  MUC search           : 0.00
% 3.01/1.47  Cooper               : 0.00
% 3.01/1.47  Total                : 0.74
% 3.01/1.47  Index Insertion      : 0.00
% 3.01/1.47  Index Deletion       : 0.00
% 3.01/1.47  Index Matching       : 0.00
% 3.01/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
