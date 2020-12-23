%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:23 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 255 expanded)
%              Number of leaves         :   39 ( 103 expanded)
%              Depth                    :   13
%              Number of atoms          :  112 ( 400 expanded)
%              Number of equality atoms :   33 ( 118 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_106,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_43,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_104,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_2,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_59,plain,(
    ! [A_43] :
      ( k1_xboole_0 = A_43
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_63,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2,c_59])).

tff(c_50,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_74,plain,(
    k3_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_63,c_50])).

tff(c_115,plain,(
    ! [A_52] :
      ( r2_hidden('#skF_3'(A_52),A_52)
      | v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_36,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,B_23)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_119,plain,(
    ! [A_52] :
      ( m1_subset_1('#skF_3'(A_52),A_52)
      | v1_relat_1(A_52) ) ),
    inference(resolution,[status(thm)],[c_115,c_36])).

tff(c_131,plain,(
    ! [B_58,A_59] :
      ( v1_xboole_0(B_58)
      | ~ m1_subset_1(B_58,A_59)
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_142,plain,(
    ! [A_65] :
      ( v1_xboole_0('#skF_3'(A_65))
      | ~ v1_xboole_0(A_65)
      | v1_relat_1(A_65) ) ),
    inference(resolution,[status(thm)],[c_119,c_131])).

tff(c_16,plain,(
    ! [A_13] :
      ( k1_xboole_0 = A_13
      | ~ v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_72,plain,(
    ! [A_13] :
      ( A_13 = '#skF_1'
      | ~ v1_xboole_0(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_16])).

tff(c_147,plain,(
    ! [A_66] :
      ( '#skF_3'(A_66) = '#skF_1'
      | ~ v1_xboole_0(A_66)
      | v1_relat_1(A_66) ) ),
    inference(resolution,[status(thm)],[c_142,c_72])).

tff(c_155,plain,
    ( '#skF_3'('#skF_1') = '#skF_1'
    | v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_147])).

tff(c_161,plain,(
    v1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    ! [A_6] : k2_xboole_0(A_6,'#skF_1') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_8])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_73,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_63,c_46])).

tff(c_48,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_75,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_63,c_48])).

tff(c_247,plain,(
    ! [A_83] :
      ( k2_xboole_0(k1_relat_1(A_83),k2_relat_1(A_83)) = k3_relat_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_256,plain,
    ( k2_xboole_0('#skF_1',k2_relat_1('#skF_1')) = k3_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_247])).

tff(c_263,plain,(
    k3_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_84,c_73,c_256])).

tff(c_265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_263])).

tff(c_267,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_309,plain,(
    ! [A_89,B_90] : k4_xboole_0(A_89,k4_xboole_0(A_89,B_90)) = k3_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_71,plain,(
    ! [A_9] : k4_xboole_0('#skF_1',A_9) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_63,c_12])).

tff(c_336,plain,(
    ! [B_91] : k3_xboole_0('#skF_1',B_91) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_71])).

tff(c_42,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_3'(A_24),A_24)
      | v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_268,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r1_xboole_0(A_84,B_85)
      | ~ r2_hidden(C_86,k3_xboole_0(A_84,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_278,plain,(
    ! [A_84,B_85] :
      ( ~ r1_xboole_0(A_84,B_85)
      | v1_relat_1(k3_xboole_0(A_84,B_85)) ) ),
    inference(resolution,[status(thm)],[c_42,c_268])).

tff(c_341,plain,(
    ! [B_91] :
      ( ~ r1_xboole_0('#skF_1',B_91)
      | v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_278])).

tff(c_348,plain,(
    ! [B_91] : ~ r1_xboole_0('#skF_1',B_91) ),
    inference(negUnitSimplification,[status(thm)],[c_267,c_341])).

tff(c_24,plain,(
    ! [B_17] : r1_tarski(k1_xboole_0,k1_tarski(B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_98,plain,(
    ! [B_17] : r1_tarski('#skF_1',k1_tarski(B_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_24])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(k1_tarski(A_14),B_15)
      | r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_352,plain,(
    ! [A_93,C_94,B_95] :
      ( r1_xboole_0(A_93,C_94)
      | ~ r1_xboole_0(B_95,C_94)
      | ~ r1_tarski(A_93,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_513,plain,(
    ! [A_116,B_117,A_118] :
      ( r1_xboole_0(A_116,B_117)
      | ~ r1_tarski(A_116,k1_tarski(A_118))
      | r2_hidden(A_118,B_117) ) ),
    inference(resolution,[status(thm)],[c_18,c_352])).

tff(c_517,plain,(
    ! [B_117,B_17] :
      ( r1_xboole_0('#skF_1',B_117)
      | r2_hidden(B_17,B_117) ) ),
    inference(resolution,[status(thm)],[c_98,c_513])).

tff(c_521,plain,(
    ! [B_17,B_117] : r2_hidden(B_17,B_117) ),
    inference(negUnitSimplification,[status(thm)],[c_348,c_517])).

tff(c_541,plain,(
    ! [A_22,B_23] : m1_subset_1(A_22,B_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_36])).

tff(c_32,plain,(
    ! [B_19,A_18] :
      ( v1_xboole_0(B_19)
      | ~ m1_subset_1(B_19,A_18)
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_554,plain,(
    ! [B_19,A_18] :
      ( v1_xboole_0(B_19)
      | ~ v1_xboole_0(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_32])).

tff(c_558,plain,(
    ! [A_18] : ~ v1_xboole_0(A_18) ),
    inference(splitLeft,[status(thm)],[c_554])).

tff(c_560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_558,c_2])).

tff(c_561,plain,(
    ! [B_19] : v1_xboole_0(B_19) ),
    inference(splitRight,[status(thm)],[c_554])).

tff(c_567,plain,(
    ! [A_130] : A_130 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_561,c_72])).

tff(c_591,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_74])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:01:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.32  
% 2.19/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 2.19/1.32  
% 2.19/1.32  %Foreground sorts:
% 2.19/1.32  
% 2.19/1.32  
% 2.19/1.32  %Background operators:
% 2.19/1.32  
% 2.19/1.32  
% 2.19/1.32  %Foreground operators:
% 2.19/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.19/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.32  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.19/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.19/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.19/1.32  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.19/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.32  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.19/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.19/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/1.32  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.19/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.19/1.32  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.19/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.32  
% 2.52/1.33  tff(f_27, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.52/1.33  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 2.52/1.33  tff(f_106, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_relat_1)).
% 2.52/1.33  tff(f_97, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.52/1.33  tff(f_87, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.52/1.33  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.52/1.33  tff(f_43, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.52/1.33  tff(f_104, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.52/1.33  tff(f_101, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.52/1.33  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.52/1.33  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.52/1.33  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.52/1.33  tff(f_68, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.52/1.33  tff(f_62, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.52/1.33  tff(f_53, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.52/1.33  tff(c_2, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.52/1.33  tff(c_59, plain, (![A_43]: (k1_xboole_0=A_43 | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.52/1.33  tff(c_63, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_2, c_59])).
% 2.52/1.33  tff(c_50, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.52/1.33  tff(c_74, plain, (k3_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_63, c_50])).
% 2.52/1.33  tff(c_115, plain, (![A_52]: (r2_hidden('#skF_3'(A_52), A_52) | v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.52/1.33  tff(c_36, plain, (![A_22, B_23]: (m1_subset_1(A_22, B_23) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.52/1.33  tff(c_119, plain, (![A_52]: (m1_subset_1('#skF_3'(A_52), A_52) | v1_relat_1(A_52))), inference(resolution, [status(thm)], [c_115, c_36])).
% 2.52/1.33  tff(c_131, plain, (![B_58, A_59]: (v1_xboole_0(B_58) | ~m1_subset_1(B_58, A_59) | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.52/1.33  tff(c_142, plain, (![A_65]: (v1_xboole_0('#skF_3'(A_65)) | ~v1_xboole_0(A_65) | v1_relat_1(A_65))), inference(resolution, [status(thm)], [c_119, c_131])).
% 2.52/1.33  tff(c_16, plain, (![A_13]: (k1_xboole_0=A_13 | ~v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.52/1.33  tff(c_72, plain, (![A_13]: (A_13='#skF_1' | ~v1_xboole_0(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_16])).
% 2.52/1.33  tff(c_147, plain, (![A_66]: ('#skF_3'(A_66)='#skF_1' | ~v1_xboole_0(A_66) | v1_relat_1(A_66))), inference(resolution, [status(thm)], [c_142, c_72])).
% 2.52/1.33  tff(c_155, plain, ('#skF_3'('#skF_1')='#skF_1' | v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2, c_147])).
% 2.52/1.33  tff(c_161, plain, (v1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_155])).
% 2.52/1.33  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.52/1.33  tff(c_84, plain, (![A_6]: (k2_xboole_0(A_6, '#skF_1')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_63, c_8])).
% 2.52/1.33  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.52/1.33  tff(c_73, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_63, c_46])).
% 2.52/1.33  tff(c_48, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.52/1.33  tff(c_75, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_63, c_48])).
% 2.52/1.33  tff(c_247, plain, (![A_83]: (k2_xboole_0(k1_relat_1(A_83), k2_relat_1(A_83))=k3_relat_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.52/1.33  tff(c_256, plain, (k2_xboole_0('#skF_1', k2_relat_1('#skF_1'))=k3_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_75, c_247])).
% 2.52/1.33  tff(c_263, plain, (k3_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_161, c_84, c_73, c_256])).
% 2.52/1.33  tff(c_265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_263])).
% 2.52/1.33  tff(c_267, plain, (~v1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_155])).
% 2.52/1.33  tff(c_309, plain, (![A_89, B_90]: (k4_xboole_0(A_89, k4_xboole_0(A_89, B_90))=k3_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.52/1.33  tff(c_12, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.52/1.33  tff(c_71, plain, (![A_9]: (k4_xboole_0('#skF_1', A_9)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_63, c_12])).
% 2.52/1.33  tff(c_336, plain, (![B_91]: (k3_xboole_0('#skF_1', B_91)='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_309, c_71])).
% 2.52/1.33  tff(c_42, plain, (![A_24]: (r2_hidden('#skF_3'(A_24), A_24) | v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.52/1.33  tff(c_268, plain, (![A_84, B_85, C_86]: (~r1_xboole_0(A_84, B_85) | ~r2_hidden(C_86, k3_xboole_0(A_84, B_85)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.52/1.33  tff(c_278, plain, (![A_84, B_85]: (~r1_xboole_0(A_84, B_85) | v1_relat_1(k3_xboole_0(A_84, B_85)))), inference(resolution, [status(thm)], [c_42, c_268])).
% 2.52/1.33  tff(c_341, plain, (![B_91]: (~r1_xboole_0('#skF_1', B_91) | v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_336, c_278])).
% 2.52/1.33  tff(c_348, plain, (![B_91]: (~r1_xboole_0('#skF_1', B_91))), inference(negUnitSimplification, [status(thm)], [c_267, c_341])).
% 2.52/1.33  tff(c_24, plain, (![B_17]: (r1_tarski(k1_xboole_0, k1_tarski(B_17)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.52/1.33  tff(c_98, plain, (![B_17]: (r1_tarski('#skF_1', k1_tarski(B_17)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_24])).
% 2.52/1.33  tff(c_18, plain, (![A_14, B_15]: (r1_xboole_0(k1_tarski(A_14), B_15) | r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.52/1.33  tff(c_352, plain, (![A_93, C_94, B_95]: (r1_xboole_0(A_93, C_94) | ~r1_xboole_0(B_95, C_94) | ~r1_tarski(A_93, B_95))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.52/1.33  tff(c_513, plain, (![A_116, B_117, A_118]: (r1_xboole_0(A_116, B_117) | ~r1_tarski(A_116, k1_tarski(A_118)) | r2_hidden(A_118, B_117))), inference(resolution, [status(thm)], [c_18, c_352])).
% 2.52/1.33  tff(c_517, plain, (![B_117, B_17]: (r1_xboole_0('#skF_1', B_117) | r2_hidden(B_17, B_117))), inference(resolution, [status(thm)], [c_98, c_513])).
% 2.52/1.33  tff(c_521, plain, (![B_17, B_117]: (r2_hidden(B_17, B_117))), inference(negUnitSimplification, [status(thm)], [c_348, c_517])).
% 2.52/1.33  tff(c_541, plain, (![A_22, B_23]: (m1_subset_1(A_22, B_23))), inference(demodulation, [status(thm), theory('equality')], [c_521, c_36])).
% 2.52/1.33  tff(c_32, plain, (![B_19, A_18]: (v1_xboole_0(B_19) | ~m1_subset_1(B_19, A_18) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.52/1.33  tff(c_554, plain, (![B_19, A_18]: (v1_xboole_0(B_19) | ~v1_xboole_0(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_541, c_32])).
% 2.52/1.33  tff(c_558, plain, (![A_18]: (~v1_xboole_0(A_18))), inference(splitLeft, [status(thm)], [c_554])).
% 2.52/1.33  tff(c_560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_558, c_2])).
% 2.52/1.33  tff(c_561, plain, (![B_19]: (v1_xboole_0(B_19))), inference(splitRight, [status(thm)], [c_554])).
% 2.52/1.33  tff(c_567, plain, (![A_130]: (A_130='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_561, c_72])).
% 2.52/1.33  tff(c_591, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_567, c_74])).
% 2.52/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.33  
% 2.52/1.33  Inference rules
% 2.52/1.33  ----------------------
% 2.52/1.33  #Ref     : 1
% 2.52/1.33  #Sup     : 114
% 2.52/1.33  #Fact    : 0
% 2.52/1.33  #Define  : 0
% 2.52/1.33  #Split   : 3
% 2.52/1.33  #Chain   : 0
% 2.52/1.33  #Close   : 0
% 2.52/1.33  
% 2.52/1.33  Ordering : KBO
% 2.52/1.33  
% 2.52/1.33  Simplification rules
% 2.52/1.33  ----------------------
% 2.52/1.33  #Subsume      : 27
% 2.52/1.33  #Demod        : 65
% 2.52/1.33  #Tautology    : 72
% 2.52/1.33  #SimpNegUnit  : 20
% 2.52/1.33  #BackRed      : 23
% 2.52/1.33  
% 2.52/1.33  #Partial instantiations: 0
% 2.52/1.33  #Strategies tried      : 1
% 2.52/1.33  
% 2.52/1.33  Timing (in seconds)
% 2.52/1.33  ----------------------
% 2.52/1.34  Preprocessing        : 0.30
% 2.52/1.34  Parsing              : 0.15
% 2.52/1.34  CNF conversion       : 0.02
% 2.52/1.34  Main loop            : 0.26
% 2.52/1.34  Inferencing          : 0.10
% 2.52/1.34  Reduction            : 0.08
% 2.52/1.34  Demodulation         : 0.05
% 2.52/1.34  BG Simplification    : 0.02
% 2.52/1.34  Subsumption          : 0.04
% 2.52/1.34  Abstraction          : 0.02
% 2.52/1.34  MUC search           : 0.00
% 2.52/1.34  Cooper               : 0.00
% 2.52/1.34  Total                : 0.59
% 2.52/1.34  Index Insertion      : 0.00
% 2.52/1.34  Index Deletion       : 0.00
% 2.52/1.34  Index Matching       : 0.00
% 2.52/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
