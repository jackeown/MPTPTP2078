%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:45 EST 2020

% Result     : Theorem 4.60s
% Output     : CNFRefutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 263 expanded)
%              Number of leaves         :   42 ( 104 expanded)
%              Depth                    :   14
%              Number of atoms          :   95 ( 453 expanded)
%              Number of equality atoms :   35 ( 116 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k5_subset_1,type,(
    k5_subset_1: ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_80,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_74,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_103,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_78,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(c_48,plain,(
    ! [A_44] : k2_subset_1(A_44) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_66,plain,(
    k4_subset_1('#skF_4','#skF_5',k2_subset_1('#skF_4')) != k2_subset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_72,plain,(
    k4_subset_1('#skF_4','#skF_5','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_66])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_203,plain,(
    ! [B_72,A_73] :
      ( v1_xboole_0(B_72)
      | ~ m1_subset_1(B_72,A_73)
      | ~ v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_217,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_68,c_203])).

tff(c_1890,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_2003,plain,(
    ! [B_260,A_261] :
      ( r2_hidden(B_260,A_261)
      | ~ m1_subset_1(B_260,A_261)
      | v1_xboole_0(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    ! [C_38,A_34] :
      ( r1_tarski(C_38,A_34)
      | ~ r2_hidden(C_38,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2022,plain,(
    ! [B_265,A_266] :
      ( r1_tarski(B_265,A_266)
      | ~ m1_subset_1(B_265,k1_zfmisc_1(A_266))
      | v1_xboole_0(k1_zfmisc_1(A_266)) ) ),
    inference(resolution,[status(thm)],[c_2003,c_24])).

tff(c_2032,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_68,c_2022])).

tff(c_2044,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1890,c_2032])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2050,plain,(
    k2_xboole_0('#skF_5','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2044,c_8])).

tff(c_52,plain,(
    ! [A_46] : m1_subset_1(k2_subset_1(A_46),k1_zfmisc_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_69,plain,(
    ! [A_46] : m1_subset_1(A_46,k1_zfmisc_1(A_46)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52])).

tff(c_3086,plain,(
    ! [A_322,B_323,C_324] :
      ( k4_subset_1(A_322,B_323,C_324) = k2_xboole_0(B_323,C_324)
      | ~ m1_subset_1(C_324,k1_zfmisc_1(A_322))
      | ~ m1_subset_1(B_323,k1_zfmisc_1(A_322)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3270,plain,(
    ! [A_330,B_331] :
      ( k4_subset_1(A_330,B_331,A_330) = k2_xboole_0(B_331,A_330)
      | ~ m1_subset_1(B_331,k1_zfmisc_1(A_330)) ) ),
    inference(resolution,[status(thm)],[c_69,c_3086])).

tff(c_3281,plain,(
    k4_subset_1('#skF_4','#skF_5','#skF_4') = k2_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_3270])).

tff(c_3293,plain,(
    k4_subset_1('#skF_4','#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2050,c_3281])).

tff(c_3295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3293])).

tff(c_3296,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_3297,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_6,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3301,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3296,c_6])).

tff(c_3358,plain,(
    ! [A_339] :
      ( A_339 = '#skF_5'
      | ~ v1_xboole_0(A_339) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3301,c_6])).

tff(c_3365,plain,(
    k1_zfmisc_1('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3297,c_3358])).

tff(c_3378,plain,(
    m1_subset_1('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3365,c_69])).

tff(c_44,plain,(
    ! [B_42,A_41] :
      ( v1_xboole_0(B_42)
      | ~ m1_subset_1(B_42,A_41)
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3395,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_3378,c_44])).

tff(c_3398,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3296,c_3395])).

tff(c_3308,plain,(
    ! [A_3] :
      ( A_3 = '#skF_5'
      | ~ v1_xboole_0(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3301,c_6])).

tff(c_3402,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3398,c_3308])).

tff(c_46,plain,(
    ! [A_43] : k1_subset_1(A_43) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_62,plain,(
    ! [A_58] : k3_subset_1(A_58,k1_subset_1(A_58)) = k2_subset_1(A_58) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_70,plain,(
    ! [A_58] : k3_subset_1(A_58,k1_subset_1(A_58)) = A_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_62])).

tff(c_74,plain,(
    ! [A_58] : k3_subset_1(A_58,k1_xboole_0) = A_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_70])).

tff(c_3306,plain,(
    ! [A_58] : k3_subset_1(A_58,'#skF_5') = A_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3301,c_74])).

tff(c_3487,plain,(
    ! [A_58] : k3_subset_1(A_58,'#skF_4') = A_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3402,c_3306])).

tff(c_50,plain,(
    ! [A_45] : m1_subset_1(k1_subset_1(A_45),k1_zfmisc_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_73,plain,(
    ! [A_45] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50])).

tff(c_3305,plain,(
    ! [A_45] : m1_subset_1('#skF_5',k1_zfmisc_1(A_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3301,c_73])).

tff(c_3410,plain,(
    ! [A_45] : m1_subset_1('#skF_4',k1_zfmisc_1(A_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3402,c_3305])).

tff(c_64,plain,(
    ! [A_59,B_60] :
      ( k4_subset_1(A_59,B_60,k3_subset_1(A_59,B_60)) = k2_subset_1(A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3808,plain,(
    ! [A_383,B_384] :
      ( k4_subset_1(A_383,B_384,k3_subset_1(A_383,B_384)) = A_383
      | ~ m1_subset_1(B_384,k1_zfmisc_1(A_383)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_64])).

tff(c_3812,plain,(
    ! [A_45] : k4_subset_1(A_45,'#skF_4',k3_subset_1(A_45,'#skF_4')) = A_45 ),
    inference(resolution,[status(thm)],[c_3410,c_3808])).

tff(c_3825,plain,(
    ! [A_45] : k4_subset_1(A_45,'#skF_4',A_45) = A_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3487,c_3812])).

tff(c_3415,plain,(
    k4_subset_1('#skF_4','#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3402,c_72])).

tff(c_3831,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3825,c_3415])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.60/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.86  
% 4.60/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.86  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 4.60/1.86  
% 4.60/1.86  %Foreground sorts:
% 4.60/1.86  
% 4.60/1.86  
% 4.60/1.86  %Background operators:
% 4.60/1.86  
% 4.60/1.86  
% 4.60/1.86  %Foreground operators:
% 4.60/1.86  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 4.60/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.60/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.60/1.86  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.60/1.86  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.60/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.60/1.86  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.60/1.86  tff(k5_subset_1, type, k5_subset_1: ($i * $i * $i) > $i).
% 4.60/1.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.60/1.86  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.60/1.86  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.60/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.60/1.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.60/1.86  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.60/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.60/1.86  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.60/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.86  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.60/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.60/1.86  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.60/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.60/1.86  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 4.60/1.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.60/1.86  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.60/1.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.60/1.86  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.60/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.60/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.60/1.86  
% 4.60/1.87  tff(f_76, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.60/1.87  tff(f_112, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 4.60/1.87  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.60/1.87  tff(f_57, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.60/1.87  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.60/1.87  tff(f_80, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.60/1.87  tff(f_95, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.60/1.87  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.60/1.87  tff(f_74, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 4.60/1.87  tff(f_103, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 4.60/1.87  tff(f_78, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 4.60/1.87  tff(f_107, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 4.60/1.87  tff(c_48, plain, (![A_44]: (k2_subset_1(A_44)=A_44)), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.60/1.87  tff(c_66, plain, (k4_subset_1('#skF_4', '#skF_5', k2_subset_1('#skF_4'))!=k2_subset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.60/1.87  tff(c_72, plain, (k4_subset_1('#skF_4', '#skF_5', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_66])).
% 4.60/1.87  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.60/1.87  tff(c_203, plain, (![B_72, A_73]: (v1_xboole_0(B_72) | ~m1_subset_1(B_72, A_73) | ~v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.60/1.87  tff(c_217, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_203])).
% 4.60/1.87  tff(c_1890, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_217])).
% 4.60/1.87  tff(c_2003, plain, (![B_260, A_261]: (r2_hidden(B_260, A_261) | ~m1_subset_1(B_260, A_261) | v1_xboole_0(A_261))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.60/1.87  tff(c_24, plain, (![C_38, A_34]: (r1_tarski(C_38, A_34) | ~r2_hidden(C_38, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.60/1.87  tff(c_2022, plain, (![B_265, A_266]: (r1_tarski(B_265, A_266) | ~m1_subset_1(B_265, k1_zfmisc_1(A_266)) | v1_xboole_0(k1_zfmisc_1(A_266)))), inference(resolution, [status(thm)], [c_2003, c_24])).
% 4.60/1.87  tff(c_2032, plain, (r1_tarski('#skF_5', '#skF_4') | v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_2022])).
% 4.60/1.87  tff(c_2044, plain, (r1_tarski('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1890, c_2032])).
% 4.60/1.87  tff(c_8, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.60/1.87  tff(c_2050, plain, (k2_xboole_0('#skF_5', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_2044, c_8])).
% 4.60/1.87  tff(c_52, plain, (![A_46]: (m1_subset_1(k2_subset_1(A_46), k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.60/1.87  tff(c_69, plain, (![A_46]: (m1_subset_1(A_46, k1_zfmisc_1(A_46)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52])).
% 4.60/1.87  tff(c_3086, plain, (![A_322, B_323, C_324]: (k4_subset_1(A_322, B_323, C_324)=k2_xboole_0(B_323, C_324) | ~m1_subset_1(C_324, k1_zfmisc_1(A_322)) | ~m1_subset_1(B_323, k1_zfmisc_1(A_322)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.60/1.87  tff(c_3270, plain, (![A_330, B_331]: (k4_subset_1(A_330, B_331, A_330)=k2_xboole_0(B_331, A_330) | ~m1_subset_1(B_331, k1_zfmisc_1(A_330)))), inference(resolution, [status(thm)], [c_69, c_3086])).
% 4.60/1.87  tff(c_3281, plain, (k4_subset_1('#skF_4', '#skF_5', '#skF_4')=k2_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_3270])).
% 4.60/1.87  tff(c_3293, plain, (k4_subset_1('#skF_4', '#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2050, c_3281])).
% 4.60/1.87  tff(c_3295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3293])).
% 4.60/1.87  tff(c_3296, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_217])).
% 4.60/1.87  tff(c_3297, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_217])).
% 4.60/1.87  tff(c_6, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.60/1.87  tff(c_3301, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3296, c_6])).
% 4.60/1.87  tff(c_3358, plain, (![A_339]: (A_339='#skF_5' | ~v1_xboole_0(A_339))), inference(demodulation, [status(thm), theory('equality')], [c_3301, c_6])).
% 4.60/1.87  tff(c_3365, plain, (k1_zfmisc_1('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_3297, c_3358])).
% 4.60/1.87  tff(c_3378, plain, (m1_subset_1('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3365, c_69])).
% 4.60/1.87  tff(c_44, plain, (![B_42, A_41]: (v1_xboole_0(B_42) | ~m1_subset_1(B_42, A_41) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.60/1.87  tff(c_3395, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_3378, c_44])).
% 4.60/1.87  tff(c_3398, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3296, c_3395])).
% 4.60/1.87  tff(c_3308, plain, (![A_3]: (A_3='#skF_5' | ~v1_xboole_0(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3301, c_6])).
% 4.60/1.87  tff(c_3402, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_3398, c_3308])).
% 4.60/1.87  tff(c_46, plain, (![A_43]: (k1_subset_1(A_43)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.60/1.87  tff(c_62, plain, (![A_58]: (k3_subset_1(A_58, k1_subset_1(A_58))=k2_subset_1(A_58))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.60/1.87  tff(c_70, plain, (![A_58]: (k3_subset_1(A_58, k1_subset_1(A_58))=A_58)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_62])).
% 4.60/1.87  tff(c_74, plain, (![A_58]: (k3_subset_1(A_58, k1_xboole_0)=A_58)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_70])).
% 4.60/1.87  tff(c_3306, plain, (![A_58]: (k3_subset_1(A_58, '#skF_5')=A_58)), inference(demodulation, [status(thm), theory('equality')], [c_3301, c_74])).
% 4.60/1.87  tff(c_3487, plain, (![A_58]: (k3_subset_1(A_58, '#skF_4')=A_58)), inference(demodulation, [status(thm), theory('equality')], [c_3402, c_3306])).
% 4.60/1.87  tff(c_50, plain, (![A_45]: (m1_subset_1(k1_subset_1(A_45), k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.60/1.87  tff(c_73, plain, (![A_45]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_45)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50])).
% 4.60/1.87  tff(c_3305, plain, (![A_45]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_45)))), inference(demodulation, [status(thm), theory('equality')], [c_3301, c_73])).
% 4.60/1.87  tff(c_3410, plain, (![A_45]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_45)))), inference(demodulation, [status(thm), theory('equality')], [c_3402, c_3305])).
% 4.60/1.87  tff(c_64, plain, (![A_59, B_60]: (k4_subset_1(A_59, B_60, k3_subset_1(A_59, B_60))=k2_subset_1(A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.60/1.87  tff(c_3808, plain, (![A_383, B_384]: (k4_subset_1(A_383, B_384, k3_subset_1(A_383, B_384))=A_383 | ~m1_subset_1(B_384, k1_zfmisc_1(A_383)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_64])).
% 4.60/1.87  tff(c_3812, plain, (![A_45]: (k4_subset_1(A_45, '#skF_4', k3_subset_1(A_45, '#skF_4'))=A_45)), inference(resolution, [status(thm)], [c_3410, c_3808])).
% 4.60/1.87  tff(c_3825, plain, (![A_45]: (k4_subset_1(A_45, '#skF_4', A_45)=A_45)), inference(demodulation, [status(thm), theory('equality')], [c_3487, c_3812])).
% 4.60/1.87  tff(c_3415, plain, (k4_subset_1('#skF_4', '#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3402, c_72])).
% 4.60/1.87  tff(c_3831, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3825, c_3415])).
% 4.60/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.87  
% 4.60/1.87  Inference rules
% 4.60/1.87  ----------------------
% 4.60/1.87  #Ref     : 0
% 4.60/1.87  #Sup     : 864
% 4.60/1.87  #Fact    : 0
% 4.60/1.87  #Define  : 0
% 4.60/1.87  #Split   : 3
% 4.60/1.87  #Chain   : 0
% 4.60/1.87  #Close   : 0
% 4.60/1.87  
% 4.60/1.87  Ordering : KBO
% 4.60/1.87  
% 4.60/1.87  Simplification rules
% 4.60/1.87  ----------------------
% 4.60/1.87  #Subsume      : 45
% 4.60/1.87  #Demod        : 283
% 4.60/1.87  #Tautology    : 541
% 4.60/1.87  #SimpNegUnit  : 11
% 4.60/1.87  #BackRed      : 23
% 4.60/1.87  
% 4.60/1.87  #Partial instantiations: 0
% 4.60/1.87  #Strategies tried      : 1
% 4.60/1.87  
% 4.60/1.87  Timing (in seconds)
% 4.60/1.87  ----------------------
% 4.60/1.88  Preprocessing        : 0.36
% 4.60/1.88  Parsing              : 0.19
% 4.60/1.88  CNF conversion       : 0.02
% 4.60/1.88  Main loop            : 0.74
% 4.60/1.88  Inferencing          : 0.28
% 4.60/1.88  Reduction            : 0.24
% 4.60/1.88  Demodulation         : 0.18
% 4.60/1.88  BG Simplification    : 0.04
% 4.60/1.88  Subsumption          : 0.12
% 4.60/1.88  Abstraction          : 0.04
% 4.60/1.88  MUC search           : 0.00
% 4.60/1.88  Cooper               : 0.00
% 4.60/1.88  Total                : 1.14
% 4.60/1.88  Index Insertion      : 0.00
% 4.60/1.88  Index Deletion       : 0.00
% 4.60/1.88  Index Matching       : 0.00
% 4.60/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
