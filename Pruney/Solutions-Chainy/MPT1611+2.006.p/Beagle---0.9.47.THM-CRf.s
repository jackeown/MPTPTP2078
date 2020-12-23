%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:32 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   77 (  92 expanded)
%              Number of leaves         :   46 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 124 expanded)
%              Number of equality atoms :   50 (  63 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_enumset1 > k2_zfmisc_1 > k1_funct_1 > k11_relat_1 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_11 > #skF_2 > #skF_8 > #skF_3 > #skF_10 > #skF_1 > #skF_7 > #skF_9 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,B)
     => k11_relat_1(k2_zfmisc_1(B,C),A) = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t203_relat_1)).

tff(f_131,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

tff(f_119,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_97,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_160,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_169,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_167,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_172,negated_conjecture,(
    ~ ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [C_21,A_17] :
      ( r2_hidden(C_21,k1_zfmisc_1(A_17))
      | ~ r1_tarski(C_21,A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_94,plain,(
    ! [A_74] : k2_zfmisc_1(A_74,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_813,plain,(
    ! [B_3153,C_3154,A_3155] :
      ( k11_relat_1(k2_zfmisc_1(B_3153,C_3154),A_3155) = C_3154
      | ~ r2_hidden(A_3155,B_3153) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_859,plain,(
    ! [A_3160,A_3161] :
      ( k11_relat_1(k1_xboole_0,A_3160) = k1_xboole_0
      | ~ r2_hidden(A_3160,A_3161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_813])).

tff(c_884,plain,(
    ! [C_3162,A_3163] :
      ( k11_relat_1(k1_xboole_0,C_3162) = k1_xboole_0
      | ~ r1_tarski(C_3162,A_3163) ) ),
    inference(resolution,[status(thm)],[c_72,c_859])).

tff(c_901,plain,(
    ! [B_2] : k11_relat_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_884])).

tff(c_116,plain,(
    ! [A_83] : k1_relat_1('#skF_8'(A_83)) = A_83 ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_120,plain,(
    ! [A_83] : v1_relat_1('#skF_8'(A_83)) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_246,plain,(
    ! [A_121] :
      ( k1_relat_1(A_121) != k1_xboole_0
      | k1_xboole_0 = A_121
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_255,plain,(
    ! [A_83] :
      ( k1_relat_1('#skF_8'(A_83)) != k1_xboole_0
      | '#skF_8'(A_83) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_120,c_246])).

tff(c_261,plain,(
    ! [A_83] :
      ( k1_xboole_0 != A_83
      | '#skF_8'(A_83) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_255])).

tff(c_914,plain,(
    ! [B_3165,A_3166] :
      ( k11_relat_1(B_3165,A_3166) != k1_xboole_0
      | ~ r2_hidden(A_3166,k1_relat_1(B_3165))
      | ~ v1_relat_1(B_3165) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_928,plain,(
    ! [A_83,A_3166] :
      ( k11_relat_1('#skF_8'(A_83),A_3166) != k1_xboole_0
      | ~ r2_hidden(A_3166,A_83)
      | ~ v1_relat_1('#skF_8'(A_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_914])).

tff(c_990,plain,(
    ! [A_3171,A_3172] :
      ( k11_relat_1('#skF_8'(A_3171),A_3172) != k1_xboole_0
      | ~ r2_hidden(A_3172,A_3171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_928])).

tff(c_993,plain,(
    ! [A_3172,A_83] :
      ( k11_relat_1(k1_xboole_0,A_3172) != k1_xboole_0
      | ~ r2_hidden(A_3172,A_83)
      | k1_xboole_0 != A_83 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_990])).

tff(c_997,plain,(
    ! [A_3173,A_3174] :
      ( ~ r2_hidden(A_3173,A_3174)
      | k1_xboole_0 != A_3174 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_901,c_993])).

tff(c_1063,plain,(
    ! [A_3180,C_3181] :
      ( k1_zfmisc_1(A_3180) != k1_xboole_0
      | ~ r1_tarski(C_3181,A_3180) ) ),
    inference(resolution,[status(thm)],[c_72,c_997])).

tff(c_1079,plain,(
    ! [B_2] : k1_zfmisc_1(B_2) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1063])).

tff(c_98,plain,(
    ! [A_76] : k3_tarski(k1_zfmisc_1(A_76)) = A_76 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_142,plain,(
    ! [A_94] : k9_setfam_1(A_94) = k1_zfmisc_1(A_94) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_146,plain,(
    ! [A_96] : k2_yellow_1(k9_setfam_1(A_96)) = k3_yellow_1(A_96) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_149,plain,(
    ! [A_96] : k2_yellow_1(k1_zfmisc_1(A_96)) = k3_yellow_1(A_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_146])).

tff(c_1080,plain,(
    ! [A_3182] :
      ( k4_yellow_0(k2_yellow_1(A_3182)) = k3_tarski(A_3182)
      | ~ r2_hidden(k3_tarski(A_3182),A_3182)
      | v1_xboole_0(A_3182) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1092,plain,(
    ! [A_17] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_17))) = k3_tarski(k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17))
      | ~ r1_tarski(k3_tarski(k1_zfmisc_1(A_17)),A_17) ) ),
    inference(resolution,[status(thm)],[c_72,c_1080])).

tff(c_1118,plain,(
    ! [A_3185] :
      ( k4_yellow_0(k3_yellow_1(A_3185)) = A_3185
      | v1_xboole_0(k1_zfmisc_1(A_3185)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_98,c_98,c_149,c_1092])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1121,plain,(
    ! [A_3185] :
      ( k1_zfmisc_1(A_3185) = k1_xboole_0
      | k4_yellow_0(k3_yellow_1(A_3185)) = A_3185 ) ),
    inference(resolution,[status(thm)],[c_1118,c_8])).

tff(c_1124,plain,(
    ! [A_3185] : k4_yellow_0(k3_yellow_1(A_3185)) = A_3185 ),
    inference(negUnitSimplification,[status(thm)],[c_1079,c_1121])).

tff(c_148,plain,(
    k4_yellow_0(k3_yellow_1('#skF_11')) != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1124,c_148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:54:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.62  
% 3.54/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.62  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_enumset1 > k2_zfmisc_1 > k1_funct_1 > k11_relat_1 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_11 > #skF_2 > #skF_8 > #skF_3 > #skF_10 > #skF_1 > #skF_7 > #skF_9 > #skF_4
% 3.54/1.62  
% 3.54/1.62  %Foreground sorts:
% 3.54/1.62  
% 3.54/1.62  
% 3.54/1.62  %Background operators:
% 3.54/1.62  
% 3.54/1.62  
% 3.54/1.62  %Foreground operators:
% 3.54/1.62  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.54/1.62  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.54/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.54/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.54/1.62  tff('#skF_11', type, '#skF_11': $i).
% 3.54/1.62  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.54/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.54/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.54/1.62  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.54/1.62  tff('#skF_8', type, '#skF_8': $i > $i).
% 3.54/1.62  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.54/1.62  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.54/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.54/1.62  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 3.54/1.62  tff('#skF_10', type, '#skF_10': $i > $i).
% 3.54/1.62  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.54/1.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.54/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.54/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.54/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.54/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.62  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.54/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.54/1.62  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 3.54/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.54/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.62  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.54/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.54/1.62  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 3.54/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.54/1.62  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.54/1.62  
% 3.54/1.63  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.54/1.63  tff(f_75, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.54/1.63  tff(f_95, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.54/1.63  tff(f_101, axiom, (![A, B, C]: (r2_hidden(A, B) => (k11_relat_1(k2_zfmisc_1(B, C), A) = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t203_relat_1)).
% 3.54/1.63  tff(f_131, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e9_44_1__funct_1)).
% 3.54/1.63  tff(f_119, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.54/1.63  tff(f_108, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.54/1.63  tff(f_97, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.54/1.63  tff(f_160, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 3.54/1.63  tff(f_169, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 3.54/1.63  tff(f_167, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 3.54/1.63  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 3.54/1.63  tff(f_172, negated_conjecture, ~(![A]: (k4_yellow_0(k3_yellow_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_yellow_1)).
% 3.54/1.63  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.54/1.63  tff(c_72, plain, (![C_21, A_17]: (r2_hidden(C_21, k1_zfmisc_1(A_17)) | ~r1_tarski(C_21, A_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.54/1.63  tff(c_94, plain, (![A_74]: (k2_zfmisc_1(A_74, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.54/1.63  tff(c_813, plain, (![B_3153, C_3154, A_3155]: (k11_relat_1(k2_zfmisc_1(B_3153, C_3154), A_3155)=C_3154 | ~r2_hidden(A_3155, B_3153))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.54/1.63  tff(c_859, plain, (![A_3160, A_3161]: (k11_relat_1(k1_xboole_0, A_3160)=k1_xboole_0 | ~r2_hidden(A_3160, A_3161))), inference(superposition, [status(thm), theory('equality')], [c_94, c_813])).
% 3.54/1.63  tff(c_884, plain, (![C_3162, A_3163]: (k11_relat_1(k1_xboole_0, C_3162)=k1_xboole_0 | ~r1_tarski(C_3162, A_3163))), inference(resolution, [status(thm)], [c_72, c_859])).
% 3.54/1.63  tff(c_901, plain, (![B_2]: (k11_relat_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_884])).
% 3.54/1.63  tff(c_116, plain, (![A_83]: (k1_relat_1('#skF_8'(A_83))=A_83)), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.54/1.63  tff(c_120, plain, (![A_83]: (v1_relat_1('#skF_8'(A_83)))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.54/1.63  tff(c_246, plain, (![A_121]: (k1_relat_1(A_121)!=k1_xboole_0 | k1_xboole_0=A_121 | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.54/1.63  tff(c_255, plain, (![A_83]: (k1_relat_1('#skF_8'(A_83))!=k1_xboole_0 | '#skF_8'(A_83)=k1_xboole_0)), inference(resolution, [status(thm)], [c_120, c_246])).
% 3.54/1.63  tff(c_261, plain, (![A_83]: (k1_xboole_0!=A_83 | '#skF_8'(A_83)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_116, c_255])).
% 3.54/1.63  tff(c_914, plain, (![B_3165, A_3166]: (k11_relat_1(B_3165, A_3166)!=k1_xboole_0 | ~r2_hidden(A_3166, k1_relat_1(B_3165)) | ~v1_relat_1(B_3165))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.54/1.63  tff(c_928, plain, (![A_83, A_3166]: (k11_relat_1('#skF_8'(A_83), A_3166)!=k1_xboole_0 | ~r2_hidden(A_3166, A_83) | ~v1_relat_1('#skF_8'(A_83)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_914])).
% 3.54/1.63  tff(c_990, plain, (![A_3171, A_3172]: (k11_relat_1('#skF_8'(A_3171), A_3172)!=k1_xboole_0 | ~r2_hidden(A_3172, A_3171))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_928])).
% 3.54/1.63  tff(c_993, plain, (![A_3172, A_83]: (k11_relat_1(k1_xboole_0, A_3172)!=k1_xboole_0 | ~r2_hidden(A_3172, A_83) | k1_xboole_0!=A_83)), inference(superposition, [status(thm), theory('equality')], [c_261, c_990])).
% 3.54/1.63  tff(c_997, plain, (![A_3173, A_3174]: (~r2_hidden(A_3173, A_3174) | k1_xboole_0!=A_3174)), inference(demodulation, [status(thm), theory('equality')], [c_901, c_993])).
% 3.54/1.63  tff(c_1063, plain, (![A_3180, C_3181]: (k1_zfmisc_1(A_3180)!=k1_xboole_0 | ~r1_tarski(C_3181, A_3180))), inference(resolution, [status(thm)], [c_72, c_997])).
% 3.54/1.63  tff(c_1079, plain, (![B_2]: (k1_zfmisc_1(B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_1063])).
% 3.54/1.63  tff(c_98, plain, (![A_76]: (k3_tarski(k1_zfmisc_1(A_76))=A_76)), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.54/1.63  tff(c_142, plain, (![A_94]: (k9_setfam_1(A_94)=k1_zfmisc_1(A_94))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.54/1.63  tff(c_146, plain, (![A_96]: (k2_yellow_1(k9_setfam_1(A_96))=k3_yellow_1(A_96))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.54/1.63  tff(c_149, plain, (![A_96]: (k2_yellow_1(k1_zfmisc_1(A_96))=k3_yellow_1(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_146])).
% 3.54/1.63  tff(c_1080, plain, (![A_3182]: (k4_yellow_0(k2_yellow_1(A_3182))=k3_tarski(A_3182) | ~r2_hidden(k3_tarski(A_3182), A_3182) | v1_xboole_0(A_3182))), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.54/1.63  tff(c_1092, plain, (![A_17]: (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_17)))=k3_tarski(k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)) | ~r1_tarski(k3_tarski(k1_zfmisc_1(A_17)), A_17))), inference(resolution, [status(thm)], [c_72, c_1080])).
% 3.54/1.63  tff(c_1118, plain, (![A_3185]: (k4_yellow_0(k3_yellow_1(A_3185))=A_3185 | v1_xboole_0(k1_zfmisc_1(A_3185)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_98, c_98, c_149, c_1092])).
% 3.54/1.63  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.54/1.63  tff(c_1121, plain, (![A_3185]: (k1_zfmisc_1(A_3185)=k1_xboole_0 | k4_yellow_0(k3_yellow_1(A_3185))=A_3185)), inference(resolution, [status(thm)], [c_1118, c_8])).
% 3.54/1.63  tff(c_1124, plain, (![A_3185]: (k4_yellow_0(k3_yellow_1(A_3185))=A_3185)), inference(negUnitSimplification, [status(thm)], [c_1079, c_1121])).
% 3.54/1.63  tff(c_148, plain, (k4_yellow_0(k3_yellow_1('#skF_11'))!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.54/1.63  tff(c_1133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1124, c_148])).
% 3.54/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.63  
% 3.54/1.63  Inference rules
% 3.54/1.63  ----------------------
% 3.54/1.63  #Ref     : 0
% 3.54/1.63  #Sup     : 246
% 3.54/1.63  #Fact    : 0
% 3.54/1.63  #Define  : 0
% 3.54/1.63  #Split   : 3
% 3.54/1.63  #Chain   : 0
% 3.54/1.63  #Close   : 0
% 3.54/1.63  
% 3.54/1.63  Ordering : KBO
% 3.54/1.63  
% 3.54/1.63  Simplification rules
% 3.54/1.63  ----------------------
% 3.54/1.63  #Subsume      : 53
% 3.54/1.63  #Demod        : 64
% 3.54/1.63  #Tautology    : 101
% 3.54/1.63  #SimpNegUnit  : 8
% 3.54/1.63  #BackRed      : 10
% 3.54/1.63  
% 3.54/1.63  #Partial instantiations: 26
% 3.54/1.63  #Strategies tried      : 1
% 3.54/1.63  
% 3.54/1.63  Timing (in seconds)
% 3.54/1.63  ----------------------
% 3.54/1.64  Preprocessing        : 0.38
% 3.54/1.64  Parsing              : 0.17
% 3.54/1.64  CNF conversion       : 0.03
% 3.54/1.64  Main loop            : 0.43
% 3.54/1.64  Inferencing          : 0.14
% 3.54/1.64  Reduction            : 0.12
% 3.54/1.64  Demodulation         : 0.08
% 3.54/1.64  BG Simplification    : 0.03
% 3.54/1.64  Subsumption          : 0.11
% 3.54/1.64  Abstraction          : 0.03
% 3.54/1.64  MUC search           : 0.00
% 3.54/1.64  Cooper               : 0.00
% 3.54/1.64  Total                : 0.84
% 3.54/1.64  Index Insertion      : 0.00
% 3.54/1.64  Index Deletion       : 0.00
% 3.54/1.64  Index Matching       : 0.00
% 3.54/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
