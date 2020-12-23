%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:26 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   76 (  96 expanded)
%              Number of leaves         :   36 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   89 ( 133 expanded)
%              Number of equality atoms :   37 (  44 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_50,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_76,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_38,plain,(
    ! [A_24] : k2_subset_1(A_24) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_48,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_51,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_48])).

tff(c_12,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_192,plain,(
    ! [A_53,B_54] : k3_tarski(k2_tarski(A_53,B_54)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_212,plain,(
    ! [A_57,B_58] : k3_tarski(k2_tarski(A_57,B_58)) = k2_xboole_0(B_58,A_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_192])).

tff(c_28,plain,(
    ! [A_20,B_21] : k3_tarski(k2_tarski(A_20,B_21)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_218,plain,(
    ! [B_58,A_57] : k2_xboole_0(B_58,A_57) = k2_xboole_0(A_57,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_28])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_44,plain,(
    ! [A_29] : ~ v1_xboole_0(k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_305,plain,(
    ! [B_69,A_70] :
      ( r2_hidden(B_69,A_70)
      | ~ m1_subset_1(B_69,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [C_19,A_15] :
      ( r1_tarski(C_19,A_15)
      | ~ r2_hidden(C_19,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_312,plain,(
    ! [B_69,A_15] :
      ( r1_tarski(B_69,A_15)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_15))
      | v1_xboole_0(k1_zfmisc_1(A_15)) ) ),
    inference(resolution,[status(thm)],[c_305,c_16])).

tff(c_322,plain,(
    ! [B_73,A_74] :
      ( r1_tarski(B_73,A_74)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_312])).

tff(c_339,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_322])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_343,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_339,c_8])).

tff(c_104,plain,(
    ! [B_39,A_40] : k3_xboole_0(B_39,A_40) = k3_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,(
    ! [A_40,B_39] : k2_xboole_0(A_40,k3_xboole_0(B_39,A_40)) = A_40 ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_6])).

tff(c_350,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_119])).

tff(c_370,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_350])).

tff(c_384,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k3_subset_1(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_401,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_384])).

tff(c_10,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_405,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_10])).

tff(c_408,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_405])).

tff(c_42,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(k3_subset_1(A_27,B_28),k1_zfmisc_1(A_27))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_336,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k3_subset_1(A_27,B_28),A_27)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(resolution,[status(thm)],[c_42,c_322])).

tff(c_18,plain,(
    ! [C_19,A_15] :
      ( r2_hidden(C_19,k1_zfmisc_1(A_15))
      | ~ r1_tarski(C_19,A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_278,plain,(
    ! [B_63,A_64] :
      ( m1_subset_1(B_63,A_64)
      | ~ r2_hidden(B_63,A_64)
      | v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_281,plain,(
    ! [C_19,A_15] :
      ( m1_subset_1(C_19,k1_zfmisc_1(A_15))
      | v1_xboole_0(k1_zfmisc_1(A_15))
      | ~ r1_tarski(C_19,A_15) ) ),
    inference(resolution,[status(thm)],[c_18,c_278])).

tff(c_284,plain,(
    ! [C_19,A_15] :
      ( m1_subset_1(C_19,k1_zfmisc_1(A_15))
      | ~ r1_tarski(C_19,A_15) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_281])).

tff(c_717,plain,(
    ! [A_105,B_106,C_107] :
      ( k4_subset_1(A_105,B_106,C_107) = k2_xboole_0(B_106,C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(A_105))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_771,plain,(
    ! [A_110,B_111,C_112] :
      ( k4_subset_1(A_110,B_111,C_112) = k2_xboole_0(B_111,C_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_110))
      | ~ r1_tarski(C_112,A_110) ) ),
    inference(resolution,[status(thm)],[c_284,c_717])).

tff(c_785,plain,(
    ! [C_113] :
      ( k4_subset_1('#skF_3','#skF_4',C_113) = k2_xboole_0('#skF_4',C_113)
      | ~ r1_tarski(C_113,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_771])).

tff(c_995,plain,(
    ! [B_129] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_129)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_129))
      | ~ m1_subset_1(B_129,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_336,c_785])).

tff(c_1014,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_995])).

tff(c_1022,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_1014])).

tff(c_1024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_1022])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:13:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.52  
% 3.14/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.52  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.14/1.52  
% 3.14/1.52  %Foreground sorts:
% 3.14/1.52  
% 3.14/1.52  
% 3.14/1.52  %Background operators:
% 3.14/1.52  
% 3.14/1.52  
% 3.14/1.52  %Foreground operators:
% 3.14/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.14/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.14/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.14/1.52  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.14/1.52  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.14/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.14/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.14/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.14/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.14/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.14/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.14/1.52  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.14/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.52  
% 3.14/1.53  tff(f_65, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.14/1.53  tff(f_87, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 3.14/1.53  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.14/1.53  tff(f_50, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.14/1.53  tff(f_76, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.14/1.53  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.14/1.53  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.14/1.53  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.14/1.53  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.14/1.53  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.14/1.53  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.14/1.53  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.14/1.53  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.14/1.53  tff(f_82, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.14/1.53  tff(c_38, plain, (![A_24]: (k2_subset_1(A_24)=A_24)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.14/1.53  tff(c_48, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.14/1.53  tff(c_51, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_48])).
% 3.14/1.53  tff(c_12, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.14/1.53  tff(c_192, plain, (![A_53, B_54]: (k3_tarski(k2_tarski(A_53, B_54))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.14/1.53  tff(c_212, plain, (![A_57, B_58]: (k3_tarski(k2_tarski(A_57, B_58))=k2_xboole_0(B_58, A_57))), inference(superposition, [status(thm), theory('equality')], [c_12, c_192])).
% 3.14/1.53  tff(c_28, plain, (![A_20, B_21]: (k3_tarski(k2_tarski(A_20, B_21))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.14/1.53  tff(c_218, plain, (![B_58, A_57]: (k2_xboole_0(B_58, A_57)=k2_xboole_0(A_57, B_58))), inference(superposition, [status(thm), theory('equality')], [c_212, c_28])).
% 3.14/1.53  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.14/1.53  tff(c_44, plain, (![A_29]: (~v1_xboole_0(k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.14/1.53  tff(c_305, plain, (![B_69, A_70]: (r2_hidden(B_69, A_70) | ~m1_subset_1(B_69, A_70) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.14/1.53  tff(c_16, plain, (![C_19, A_15]: (r1_tarski(C_19, A_15) | ~r2_hidden(C_19, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.14/1.53  tff(c_312, plain, (![B_69, A_15]: (r1_tarski(B_69, A_15) | ~m1_subset_1(B_69, k1_zfmisc_1(A_15)) | v1_xboole_0(k1_zfmisc_1(A_15)))), inference(resolution, [status(thm)], [c_305, c_16])).
% 3.14/1.53  tff(c_322, plain, (![B_73, A_74]: (r1_tarski(B_73, A_74) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)))), inference(negUnitSimplification, [status(thm)], [c_44, c_312])).
% 3.14/1.53  tff(c_339, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_322])).
% 3.14/1.53  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.14/1.53  tff(c_343, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_339, c_8])).
% 3.14/1.53  tff(c_104, plain, (![B_39, A_40]: (k3_xboole_0(B_39, A_40)=k3_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.14/1.53  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.14/1.53  tff(c_119, plain, (![A_40, B_39]: (k2_xboole_0(A_40, k3_xboole_0(B_39, A_40))=A_40)), inference(superposition, [status(thm), theory('equality')], [c_104, c_6])).
% 3.14/1.53  tff(c_350, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_343, c_119])).
% 3.14/1.53  tff(c_370, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_218, c_350])).
% 3.14/1.53  tff(c_384, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k3_subset_1(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.14/1.53  tff(c_401, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_384])).
% 3.14/1.53  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.14/1.53  tff(c_405, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_401, c_10])).
% 3.14/1.53  tff(c_408, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_370, c_405])).
% 3.14/1.53  tff(c_42, plain, (![A_27, B_28]: (m1_subset_1(k3_subset_1(A_27, B_28), k1_zfmisc_1(A_27)) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.14/1.53  tff(c_336, plain, (![A_27, B_28]: (r1_tarski(k3_subset_1(A_27, B_28), A_27) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(resolution, [status(thm)], [c_42, c_322])).
% 3.14/1.53  tff(c_18, plain, (![C_19, A_15]: (r2_hidden(C_19, k1_zfmisc_1(A_15)) | ~r1_tarski(C_19, A_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.14/1.53  tff(c_278, plain, (![B_63, A_64]: (m1_subset_1(B_63, A_64) | ~r2_hidden(B_63, A_64) | v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.14/1.53  tff(c_281, plain, (![C_19, A_15]: (m1_subset_1(C_19, k1_zfmisc_1(A_15)) | v1_xboole_0(k1_zfmisc_1(A_15)) | ~r1_tarski(C_19, A_15))), inference(resolution, [status(thm)], [c_18, c_278])).
% 3.14/1.53  tff(c_284, plain, (![C_19, A_15]: (m1_subset_1(C_19, k1_zfmisc_1(A_15)) | ~r1_tarski(C_19, A_15))), inference(negUnitSimplification, [status(thm)], [c_44, c_281])).
% 3.14/1.53  tff(c_717, plain, (![A_105, B_106, C_107]: (k4_subset_1(A_105, B_106, C_107)=k2_xboole_0(B_106, C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(A_105)) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.14/1.53  tff(c_771, plain, (![A_110, B_111, C_112]: (k4_subset_1(A_110, B_111, C_112)=k2_xboole_0(B_111, C_112) | ~m1_subset_1(B_111, k1_zfmisc_1(A_110)) | ~r1_tarski(C_112, A_110))), inference(resolution, [status(thm)], [c_284, c_717])).
% 3.14/1.53  tff(c_785, plain, (![C_113]: (k4_subset_1('#skF_3', '#skF_4', C_113)=k2_xboole_0('#skF_4', C_113) | ~r1_tarski(C_113, '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_771])).
% 3.14/1.53  tff(c_995, plain, (![B_129]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_129))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_129)) | ~m1_subset_1(B_129, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_336, c_785])).
% 3.14/1.53  tff(c_1014, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_995])).
% 3.14/1.53  tff(c_1022, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_408, c_1014])).
% 3.14/1.53  tff(c_1024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_1022])).
% 3.14/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.53  
% 3.14/1.53  Inference rules
% 3.14/1.53  ----------------------
% 3.14/1.53  #Ref     : 0
% 3.14/1.53  #Sup     : 233
% 3.14/1.53  #Fact    : 0
% 3.14/1.53  #Define  : 0
% 3.14/1.53  #Split   : 0
% 3.14/1.53  #Chain   : 0
% 3.14/1.53  #Close   : 0
% 3.14/1.53  
% 3.14/1.53  Ordering : KBO
% 3.14/1.53  
% 3.14/1.53  Simplification rules
% 3.14/1.53  ----------------------
% 3.14/1.53  #Subsume      : 15
% 3.14/1.53  #Demod        : 52
% 3.14/1.53  #Tautology    : 132
% 3.14/1.53  #SimpNegUnit  : 13
% 3.14/1.53  #BackRed      : 1
% 3.14/1.53  
% 3.14/1.53  #Partial instantiations: 0
% 3.14/1.53  #Strategies tried      : 1
% 3.14/1.53  
% 3.14/1.53  Timing (in seconds)
% 3.14/1.53  ----------------------
% 3.14/1.54  Preprocessing        : 0.32
% 3.14/1.54  Parsing              : 0.17
% 3.14/1.54  CNF conversion       : 0.02
% 3.14/1.54  Main loop            : 0.39
% 3.14/1.54  Inferencing          : 0.16
% 3.14/1.54  Reduction            : 0.12
% 3.14/1.54  Demodulation         : 0.09
% 3.14/1.54  BG Simplification    : 0.02
% 3.14/1.54  Subsumption          : 0.07
% 3.14/1.54  Abstraction          : 0.02
% 3.14/1.54  MUC search           : 0.00
% 3.14/1.54  Cooper               : 0.00
% 3.14/1.54  Total                : 0.75
% 3.14/1.54  Index Insertion      : 0.00
% 3.14/1.54  Index Deletion       : 0.00
% 3.14/1.54  Index Matching       : 0.00
% 3.14/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
