%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:35 EST 2020

% Result     : Theorem 22.56s
% Output     : CNFRefutation 22.56s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 125 expanded)
%              Number of leaves         :   38 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :   95 ( 174 expanded)
%              Number of equality atoms :   33 (  61 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_86,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_60,plain,(
    ! [A_33] : k2_subset_1(A_33) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_68,plain,(
    k4_subset_1('#skF_6','#skF_7',k3_subset_1('#skF_6','#skF_7')) != k2_subset_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_71,plain,(
    k4_subset_1('#skF_6','#skF_7',k3_subset_1('#skF_6','#skF_7')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_68])).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_64,plain,(
    ! [A_36] : ~ v1_xboole_0(k1_zfmisc_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_168,plain,(
    ! [B_63,A_64] :
      ( r2_hidden(B_63,A_64)
      | ~ m1_subset_1(B_63,A_64)
      | v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38,plain,(
    ! [C_28,A_24] :
      ( r1_tarski(C_28,A_24)
      | ~ r2_hidden(C_28,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_176,plain,(
    ! [B_63,A_24] :
      ( r1_tarski(B_63,A_24)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_24))
      | v1_xboole_0(k1_zfmisc_1(A_24)) ) ),
    inference(resolution,[status(thm)],[c_168,c_38])).

tff(c_196,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(B_67,A_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_176])).

tff(c_205,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_196])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_209,plain,(
    k3_xboole_0('#skF_7','#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_205,c_30])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_216,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_2])).

tff(c_554,plain,(
    ! [A_95,B_96] :
      ( k4_xboole_0(A_95,B_96) = k3_subset_1(A_95,B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_567,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k3_subset_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_554])).

tff(c_273,plain,(
    ! [A_73,B_74] : k2_xboole_0(k3_xboole_0(A_73,B_74),k4_xboole_0(A_73,B_74)) = A_73 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_291,plain,(
    ! [B_2,A_1] : k2_xboole_0(k3_xboole_0(B_2,A_1),k4_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_273])).

tff(c_573,plain,(
    k2_xboole_0(k3_xboole_0('#skF_7','#skF_6'),k3_subset_1('#skF_6','#skF_7')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_291])).

tff(c_582,plain,(
    k2_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_2,c_573])).

tff(c_32,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_579,plain,(
    k4_xboole_0('#skF_6',k3_subset_1('#skF_6','#skF_7')) = k3_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_32])).

tff(c_584,plain,(
    k4_xboole_0('#skF_6',k3_subset_1('#skF_6','#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_579])).

tff(c_600,plain,(
    k3_xboole_0('#skF_6',k3_subset_1('#skF_6','#skF_7')) = k4_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_32])).

tff(c_604,plain,(
    k3_xboole_0('#skF_6',k3_subset_1('#skF_6','#skF_7')) = k3_subset_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_600])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_250,plain,(
    ! [D_70,B_71,A_72] :
      ( r2_hidden(D_70,B_71)
      | ~ r2_hidden(D_70,k3_xboole_0(A_72,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2533,plain,(
    ! [A_207,B_208,B_209] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_207,B_208),B_209),B_208)
      | r1_tarski(k3_xboole_0(A_207,B_208),B_209) ) ),
    inference(resolution,[status(thm)],[c_8,c_250])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2615,plain,(
    ! [A_210,B_211] : r1_tarski(k3_xboole_0(A_210,B_211),B_211) ),
    inference(resolution,[status(thm)],[c_2533,c_6])).

tff(c_2681,plain,(
    ! [B_212,A_213] : r1_tarski(k3_xboole_0(B_212,A_213),B_212) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2615])).

tff(c_2717,plain,(
    r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_2681])).

tff(c_40,plain,(
    ! [C_28,A_24] :
      ( r2_hidden(C_28,k1_zfmisc_1(A_24))
      | ~ r1_tarski(C_28,A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_305,plain,(
    ! [B_75,A_76] :
      ( m1_subset_1(B_75,A_76)
      | ~ r2_hidden(B_75,A_76)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_314,plain,(
    ! [C_28,A_24] :
      ( m1_subset_1(C_28,k1_zfmisc_1(A_24))
      | v1_xboole_0(k1_zfmisc_1(A_24))
      | ~ r1_tarski(C_28,A_24) ) ),
    inference(resolution,[status(thm)],[c_40,c_305])).

tff(c_319,plain,(
    ! [C_28,A_24] :
      ( m1_subset_1(C_28,k1_zfmisc_1(A_24))
      | ~ r1_tarski(C_28,A_24) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_314])).

tff(c_1300,plain,(
    ! [A_142,B_143,C_144] :
      ( k4_subset_1(A_142,B_143,C_144) = k2_xboole_0(B_143,C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(A_142))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(A_142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_65011,plain,(
    ! [A_1087,B_1088,C_1089] :
      ( k4_subset_1(A_1087,B_1088,C_1089) = k2_xboole_0(B_1088,C_1089)
      | ~ m1_subset_1(B_1088,k1_zfmisc_1(A_1087))
      | ~ r1_tarski(C_1089,A_1087) ) ),
    inference(resolution,[status(thm)],[c_319,c_1300])).

tff(c_65109,plain,(
    ! [C_1090] :
      ( k4_subset_1('#skF_6','#skF_7',C_1090) = k2_xboole_0('#skF_7',C_1090)
      | ~ r1_tarski(C_1090,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_70,c_65011])).

tff(c_65201,plain,(
    k4_subset_1('#skF_6','#skF_7',k3_subset_1('#skF_6','#skF_7')) = k2_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_2717,c_65109])).

tff(c_65262,plain,(
    k4_subset_1('#skF_6','#skF_7',k3_subset_1('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_65201])).

tff(c_65264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_65262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.56/13.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.56/13.08  
% 22.56/13.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.56/13.08  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 22.56/13.08  
% 22.56/13.08  %Foreground sorts:
% 22.56/13.08  
% 22.56/13.08  
% 22.56/13.08  %Background operators:
% 22.56/13.08  
% 22.56/13.08  
% 22.56/13.08  %Foreground operators:
% 22.56/13.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.56/13.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.56/13.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 22.56/13.08  tff('#skF_7', type, '#skF_7': $i).
% 22.56/13.08  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 22.56/13.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.56/13.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.56/13.08  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 22.56/13.08  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 22.56/13.08  tff('#skF_6', type, '#skF_6': $i).
% 22.56/13.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 22.56/13.08  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 22.56/13.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.56/13.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.56/13.08  tff(k3_tarski, type, k3_tarski: $i > $i).
% 22.56/13.08  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 22.56/13.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.56/13.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 22.56/13.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 22.56/13.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 22.56/13.08  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 22.56/13.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 22.56/13.08  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 22.56/13.08  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 22.56/13.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.56/13.08  
% 22.56/13.10  tff(f_79, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 22.56/13.10  tff(f_97, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 22.56/13.10  tff(f_86, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 22.56/13.10  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 22.56/13.10  tff(f_62, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 22.56/13.10  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 22.56/13.10  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 22.56/13.10  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 22.56/13.10  tff(f_53, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 22.56/13.10  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 22.56/13.10  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 22.56/13.10  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 22.56/13.10  tff(f_92, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 22.56/13.10  tff(c_60, plain, (![A_33]: (k2_subset_1(A_33)=A_33)), inference(cnfTransformation, [status(thm)], [f_79])).
% 22.56/13.10  tff(c_68, plain, (k4_subset_1('#skF_6', '#skF_7', k3_subset_1('#skF_6', '#skF_7'))!=k2_subset_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 22.56/13.10  tff(c_71, plain, (k4_subset_1('#skF_6', '#skF_7', k3_subset_1('#skF_6', '#skF_7'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_68])).
% 22.56/13.10  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 22.56/13.10  tff(c_64, plain, (![A_36]: (~v1_xboole_0(k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 22.56/13.10  tff(c_168, plain, (![B_63, A_64]: (r2_hidden(B_63, A_64) | ~m1_subset_1(B_63, A_64) | v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_77])).
% 22.56/13.10  tff(c_38, plain, (![C_28, A_24]: (r1_tarski(C_28, A_24) | ~r2_hidden(C_28, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 22.56/13.10  tff(c_176, plain, (![B_63, A_24]: (r1_tarski(B_63, A_24) | ~m1_subset_1(B_63, k1_zfmisc_1(A_24)) | v1_xboole_0(k1_zfmisc_1(A_24)))), inference(resolution, [status(thm)], [c_168, c_38])).
% 22.56/13.10  tff(c_196, plain, (![B_67, A_68]: (r1_tarski(B_67, A_68) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)))), inference(negUnitSimplification, [status(thm)], [c_64, c_176])).
% 22.56/13.10  tff(c_205, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_70, c_196])).
% 22.56/13.10  tff(c_30, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.56/13.10  tff(c_209, plain, (k3_xboole_0('#skF_7', '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_205, c_30])).
% 22.56/13.10  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 22.56/13.10  tff(c_216, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_209, c_2])).
% 22.56/13.10  tff(c_554, plain, (![A_95, B_96]: (k4_xboole_0(A_95, B_96)=k3_subset_1(A_95, B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 22.56/13.10  tff(c_567, plain, (k4_xboole_0('#skF_6', '#skF_7')=k3_subset_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_70, c_554])).
% 22.56/13.10  tff(c_273, plain, (![A_73, B_74]: (k2_xboole_0(k3_xboole_0(A_73, B_74), k4_xboole_0(A_73, B_74))=A_73)), inference(cnfTransformation, [status(thm)], [f_53])).
% 22.56/13.10  tff(c_291, plain, (![B_2, A_1]: (k2_xboole_0(k3_xboole_0(B_2, A_1), k4_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_273])).
% 22.56/13.10  tff(c_573, plain, (k2_xboole_0(k3_xboole_0('#skF_7', '#skF_6'), k3_subset_1('#skF_6', '#skF_7'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_567, c_291])).
% 22.56/13.10  tff(c_582, plain, (k2_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_216, c_2, c_573])).
% 22.56/13.10  tff(c_32, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 22.56/13.10  tff(c_579, plain, (k4_xboole_0('#skF_6', k3_subset_1('#skF_6', '#skF_7'))=k3_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_567, c_32])).
% 22.56/13.10  tff(c_584, plain, (k4_xboole_0('#skF_6', k3_subset_1('#skF_6', '#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_216, c_579])).
% 22.56/13.10  tff(c_600, plain, (k3_xboole_0('#skF_6', k3_subset_1('#skF_6', '#skF_7'))=k4_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_584, c_32])).
% 22.56/13.10  tff(c_604, plain, (k3_xboole_0('#skF_6', k3_subset_1('#skF_6', '#skF_7'))=k3_subset_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_567, c_600])).
% 22.56/13.10  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 22.56/13.10  tff(c_250, plain, (![D_70, B_71, A_72]: (r2_hidden(D_70, B_71) | ~r2_hidden(D_70, k3_xboole_0(A_72, B_71)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 22.56/13.10  tff(c_2533, plain, (![A_207, B_208, B_209]: (r2_hidden('#skF_1'(k3_xboole_0(A_207, B_208), B_209), B_208) | r1_tarski(k3_xboole_0(A_207, B_208), B_209))), inference(resolution, [status(thm)], [c_8, c_250])).
% 22.56/13.10  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 22.56/13.10  tff(c_2615, plain, (![A_210, B_211]: (r1_tarski(k3_xboole_0(A_210, B_211), B_211))), inference(resolution, [status(thm)], [c_2533, c_6])).
% 22.56/13.10  tff(c_2681, plain, (![B_212, A_213]: (r1_tarski(k3_xboole_0(B_212, A_213), B_212))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2615])).
% 22.56/13.10  tff(c_2717, plain, (r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_604, c_2681])).
% 22.56/13.10  tff(c_40, plain, (![C_28, A_24]: (r2_hidden(C_28, k1_zfmisc_1(A_24)) | ~r1_tarski(C_28, A_24))), inference(cnfTransformation, [status(thm)], [f_62])).
% 22.56/13.10  tff(c_305, plain, (![B_75, A_76]: (m1_subset_1(B_75, A_76) | ~r2_hidden(B_75, A_76) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_77])).
% 22.56/13.10  tff(c_314, plain, (![C_28, A_24]: (m1_subset_1(C_28, k1_zfmisc_1(A_24)) | v1_xboole_0(k1_zfmisc_1(A_24)) | ~r1_tarski(C_28, A_24))), inference(resolution, [status(thm)], [c_40, c_305])).
% 22.56/13.10  tff(c_319, plain, (![C_28, A_24]: (m1_subset_1(C_28, k1_zfmisc_1(A_24)) | ~r1_tarski(C_28, A_24))), inference(negUnitSimplification, [status(thm)], [c_64, c_314])).
% 22.56/13.10  tff(c_1300, plain, (![A_142, B_143, C_144]: (k4_subset_1(A_142, B_143, C_144)=k2_xboole_0(B_143, C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(A_142)) | ~m1_subset_1(B_143, k1_zfmisc_1(A_142)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 22.56/13.10  tff(c_65011, plain, (![A_1087, B_1088, C_1089]: (k4_subset_1(A_1087, B_1088, C_1089)=k2_xboole_0(B_1088, C_1089) | ~m1_subset_1(B_1088, k1_zfmisc_1(A_1087)) | ~r1_tarski(C_1089, A_1087))), inference(resolution, [status(thm)], [c_319, c_1300])).
% 22.56/13.10  tff(c_65109, plain, (![C_1090]: (k4_subset_1('#skF_6', '#skF_7', C_1090)=k2_xboole_0('#skF_7', C_1090) | ~r1_tarski(C_1090, '#skF_6'))), inference(resolution, [status(thm)], [c_70, c_65011])).
% 22.56/13.10  tff(c_65201, plain, (k4_subset_1('#skF_6', '#skF_7', k3_subset_1('#skF_6', '#skF_7'))=k2_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_2717, c_65109])).
% 22.56/13.10  tff(c_65262, plain, (k4_subset_1('#skF_6', '#skF_7', k3_subset_1('#skF_6', '#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_582, c_65201])).
% 22.56/13.10  tff(c_65264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_65262])).
% 22.56/13.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.56/13.10  
% 22.56/13.10  Inference rules
% 22.56/13.10  ----------------------
% 22.56/13.10  #Ref     : 0
% 22.56/13.10  #Sup     : 15417
% 22.56/13.10  #Fact    : 0
% 22.56/13.10  #Define  : 0
% 22.56/13.10  #Split   : 11
% 22.56/13.10  #Chain   : 0
% 22.56/13.10  #Close   : 0
% 22.56/13.10  
% 22.56/13.10  Ordering : KBO
% 22.56/13.10  
% 22.56/13.10  Simplification rules
% 22.56/13.10  ----------------------
% 22.56/13.10  #Subsume      : 2920
% 22.56/13.10  #Demod        : 20556
% 22.56/13.10  #Tautology    : 5430
% 22.56/13.10  #SimpNegUnit  : 233
% 22.56/13.10  #BackRed      : 109
% 22.56/13.10  
% 22.56/13.10  #Partial instantiations: 0
% 22.56/13.10  #Strategies tried      : 1
% 22.56/13.10  
% 22.56/13.10  Timing (in seconds)
% 22.56/13.10  ----------------------
% 22.56/13.10  Preprocessing        : 0.32
% 22.56/13.10  Parsing              : 0.16
% 22.56/13.10  CNF conversion       : 0.02
% 22.56/13.10  Main loop            : 12.03
% 22.56/13.10  Inferencing          : 1.75
% 22.56/13.10  Reduction            : 6.34
% 22.56/13.10  Demodulation         : 5.62
% 22.56/13.10  BG Simplification    : 0.21
% 22.56/13.10  Subsumption          : 3.15
% 22.56/13.10  Abstraction          : 0.37
% 22.56/13.10  MUC search           : 0.00
% 22.56/13.10  Cooper               : 0.00
% 22.56/13.10  Total                : 12.38
% 22.56/13.10  Index Insertion      : 0.00
% 22.56/13.10  Index Deletion       : 0.00
% 22.56/13.10  Index Matching       : 0.00
% 22.56/13.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
