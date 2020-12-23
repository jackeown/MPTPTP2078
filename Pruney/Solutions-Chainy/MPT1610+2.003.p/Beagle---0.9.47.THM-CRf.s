%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:29 EST 2020

% Result     : Theorem 4.81s
% Output     : CNFRefutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 116 expanded)
%              Number of leaves         :   50 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  105 ( 187 expanded)
%              Number of equality atoms :   59 ( 100 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_enumset1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > k11_relat_1 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k3_tarski > k3_lattice3 > k2_yellow_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_lattice3 > k1_xboole_0 > #skF_9 > #skF_5 > #skF_6 > #skF_1 > #skF_11 > #skF_3 > #skF_2 > #skF_10 > #skF_8 > #skF_7 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k8_enumset1,type,(
    k8_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_112,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_137,axiom,(
    ! [A,B] :
      ~ ( ~ ( A = k1_xboole_0
            & B != k1_xboole_0 )
        & ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ~ ( B = k1_relat_1(C)
                & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_120,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_98,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,B)
     => k11_relat_1(k2_zfmisc_1(B,C),A) = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t203_relat_1)).

tff(f_165,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e15_31__wellord2)).

tff(f_109,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_167,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_178,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_176,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_181,negated_conjecture,(
    ~ ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).

tff(c_110,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_122,plain,(
    ! [A_83] : k1_relat_1('#skF_8'(A_83,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_130,plain,(
    ! [A_83] : v1_relat_1('#skF_8'(A_83,k1_xboole_0)) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_286,plain,(
    ! [A_132] :
      ( k1_relat_1(A_132) != k1_xboole_0
      | k1_xboole_0 = A_132
      | ~ v1_relat_1(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_292,plain,(
    ! [A_83] :
      ( k1_relat_1('#skF_8'(A_83,k1_xboole_0)) != k1_xboole_0
      | '#skF_8'(A_83,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_130,c_286])).

tff(c_299,plain,(
    ! [A_83] : '#skF_8'(A_83,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_292])).

tff(c_118,plain,(
    ! [A_83] : r1_tarski(k2_relat_1('#skF_8'(A_83,k1_xboole_0)),A_83) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_312,plain,(
    ! [A_83] : r1_tarski(k2_relat_1(k1_xboole_0),A_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_118])).

tff(c_316,plain,(
    ! [A_83] : r1_tarski(k1_xboole_0,A_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_312])).

tff(c_78,plain,(
    ! [C_22,A_18] :
      ( r2_hidden(C_22,k1_zfmisc_1(A_18))
      | ~ r1_tarski(C_22,A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_100,plain,(
    ! [A_75] : k2_zfmisc_1(A_75,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_426,plain,(
    ! [B_148,C_149,A_150] :
      ( k11_relat_1(k2_zfmisc_1(B_148,C_149),A_150) = C_149
      | ~ r2_hidden(A_150,B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_447,plain,(
    ! [A_153,A_154] :
      ( k11_relat_1(k1_xboole_0,A_153) = k1_xboole_0
      | ~ r2_hidden(A_153,A_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_426])).

tff(c_460,plain,(
    ! [C_155,A_156] :
      ( k11_relat_1(k1_xboole_0,C_155) = k1_xboole_0
      | ~ r1_tarski(C_155,A_156) ) ),
    inference(resolution,[status(thm)],[c_78,c_447])).

tff(c_472,plain,(
    ! [B_3] : k11_relat_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_460])).

tff(c_142,plain,(
    ! [A_96] : k1_relat_1('#skF_10'(A_96)) = A_96 ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_146,plain,(
    ! [A_96] : v1_relat_1('#skF_10'(A_96)) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_295,plain,(
    ! [A_96] :
      ( k1_relat_1('#skF_10'(A_96)) != k1_xboole_0
      | '#skF_10'(A_96) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_146,c_286])).

tff(c_301,plain,(
    ! [A_96] :
      ( k1_xboole_0 != A_96
      | '#skF_10'(A_96) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_295])).

tff(c_713,plain,(
    ! [B_183,A_184] :
      ( k11_relat_1(B_183,A_184) != k1_xboole_0
      | ~ r2_hidden(A_184,k1_relat_1(B_183))
      | ~ v1_relat_1(B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_730,plain,(
    ! [A_96,A_184] :
      ( k11_relat_1('#skF_10'(A_96),A_184) != k1_xboole_0
      | ~ r2_hidden(A_184,A_96)
      | ~ v1_relat_1('#skF_10'(A_96)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_713])).

tff(c_741,plain,(
    ! [A_185,A_186] :
      ( k11_relat_1('#skF_10'(A_185),A_186) != k1_xboole_0
      | ~ r2_hidden(A_186,A_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_730])).

tff(c_747,plain,(
    ! [A_186,A_96] :
      ( k11_relat_1(k1_xboole_0,A_186) != k1_xboole_0
      | ~ r2_hidden(A_186,A_96)
      | k1_xboole_0 != A_96 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_741])).

tff(c_752,plain,(
    ! [A_187,A_188] :
      ( ~ r2_hidden(A_187,A_188)
      | k1_xboole_0 != A_188 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_747])).

tff(c_821,plain,(
    ! [A_194,C_195] :
      ( k1_zfmisc_1(A_194) != k1_xboole_0
      | ~ r1_tarski(C_195,A_194) ) ),
    inference(resolution,[status(thm)],[c_78,c_752])).

tff(c_836,plain,(
    ! [A_83] : k1_zfmisc_1(A_83) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_316,c_821])).

tff(c_148,plain,(
    ! [A_102] : k9_setfam_1(A_102) = k1_zfmisc_1(A_102) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_154,plain,(
    ! [A_105] : k2_yellow_1(k9_setfam_1(A_105)) = k3_yellow_1(A_105) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_157,plain,(
    ! [A_105] : k2_yellow_1(k1_zfmisc_1(A_105)) = k3_yellow_1(A_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_154])).

tff(c_488,plain,(
    ! [A_158] :
      ( k3_yellow_0(k2_yellow_1(A_158)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_158)
      | v1_xboole_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_3602,plain,(
    ! [A_6946] :
      ( k3_yellow_0(k3_yellow_1(A_6946)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_6946))
      | v1_xboole_0(k1_zfmisc_1(A_6946)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_488])).

tff(c_3629,plain,(
    ! [A_18] :
      ( k3_yellow_0(k3_yellow_1(A_18)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_18))
      | ~ r1_tarski(k1_xboole_0,A_18) ) ),
    inference(resolution,[status(thm)],[c_78,c_3602])).

tff(c_3634,plain,(
    ! [A_7011] :
      ( k3_yellow_0(k3_yellow_1(A_7011)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_7011)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_3629])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3637,plain,(
    ! [A_7011] :
      ( k1_zfmisc_1(A_7011) = k1_xboole_0
      | k3_yellow_0(k3_yellow_1(A_7011)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3634,c_2])).

tff(c_3679,plain,(
    ! [A_7011] : k3_yellow_0(k3_yellow_1(A_7011)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_836,c_3637])).

tff(c_156,plain,(
    k3_yellow_0(k3_yellow_1('#skF_11')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_3685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3679,c_156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:26:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.81/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.14/1.88  
% 5.14/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.14/1.89  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_enumset1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > k11_relat_1 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k3_tarski > k3_lattice3 > k2_yellow_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_lattice3 > k1_xboole_0 > #skF_9 > #skF_5 > #skF_6 > #skF_1 > #skF_11 > #skF_3 > #skF_2 > #skF_10 > #skF_8 > #skF_7 > #skF_4
% 5.14/1.89  
% 5.14/1.89  %Foreground sorts:
% 5.14/1.89  
% 5.14/1.89  
% 5.14/1.89  %Background operators:
% 5.14/1.89  
% 5.14/1.89  
% 5.14/1.89  %Foreground operators:
% 5.14/1.89  tff('#skF_9', type, '#skF_9': $i > $i).
% 5.14/1.89  tff('#skF_5', type, '#skF_5': $i > $i).
% 5.14/1.89  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.14/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.14/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.14/1.89  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 5.14/1.89  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.14/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.14/1.89  tff('#skF_11', type, '#skF_11': $i).
% 5.14/1.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.14/1.89  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 5.14/1.89  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.14/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.14/1.89  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 5.14/1.89  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 5.14/1.89  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.14/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.14/1.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.14/1.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.14/1.89  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 5.14/1.89  tff('#skF_10', type, '#skF_10': $i > $i).
% 5.14/1.89  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 5.14/1.89  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 5.14/1.89  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 5.14/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.14/1.89  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.14/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.14/1.89  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.14/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.14/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.14/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.14/1.89  tff(k8_enumset1, type, k8_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.14/1.89  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 5.14/1.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.14/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.14/1.89  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.14/1.89  
% 5.14/1.90  tff(f_112, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.14/1.90  tff(f_137, axiom, (![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 5.14/1.90  tff(f_120, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 5.14/1.90  tff(f_78, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.14/1.90  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.14/1.90  tff(f_98, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.14/1.90  tff(f_102, axiom, (![A, B, C]: (r2_hidden(A, B) => (k11_relat_1(k2_zfmisc_1(B, C), A) = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t203_relat_1)).
% 5.14/1.90  tff(f_165, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_tarski(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e15_31__wellord2)).
% 5.14/1.90  tff(f_109, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 5.14/1.90  tff(f_167, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 5.14/1.90  tff(f_178, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 5.14/1.90  tff(f_176, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 5.14/1.90  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.14/1.90  tff(f_181, negated_conjecture, ~(![A]: (k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_yellow_1)).
% 5.14/1.90  tff(c_110, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.14/1.90  tff(c_122, plain, (![A_83]: (k1_relat_1('#skF_8'(A_83, k1_xboole_0))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.14/1.90  tff(c_130, plain, (![A_83]: (v1_relat_1('#skF_8'(A_83, k1_xboole_0)))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.14/1.90  tff(c_286, plain, (![A_132]: (k1_relat_1(A_132)!=k1_xboole_0 | k1_xboole_0=A_132 | ~v1_relat_1(A_132))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.14/1.90  tff(c_292, plain, (![A_83]: (k1_relat_1('#skF_8'(A_83, k1_xboole_0))!=k1_xboole_0 | '#skF_8'(A_83, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_130, c_286])).
% 5.14/1.90  tff(c_299, plain, (![A_83]: ('#skF_8'(A_83, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_292])).
% 5.14/1.90  tff(c_118, plain, (![A_83]: (r1_tarski(k2_relat_1('#skF_8'(A_83, k1_xboole_0)), A_83))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.14/1.90  tff(c_312, plain, (![A_83]: (r1_tarski(k2_relat_1(k1_xboole_0), A_83))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_118])).
% 5.14/1.90  tff(c_316, plain, (![A_83]: (r1_tarski(k1_xboole_0, A_83))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_312])).
% 5.14/1.90  tff(c_78, plain, (![C_22, A_18]: (r2_hidden(C_22, k1_zfmisc_1(A_18)) | ~r1_tarski(C_22, A_18))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.14/1.90  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.14/1.90  tff(c_100, plain, (![A_75]: (k2_zfmisc_1(A_75, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.14/1.90  tff(c_426, plain, (![B_148, C_149, A_150]: (k11_relat_1(k2_zfmisc_1(B_148, C_149), A_150)=C_149 | ~r2_hidden(A_150, B_148))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.14/1.90  tff(c_447, plain, (![A_153, A_154]: (k11_relat_1(k1_xboole_0, A_153)=k1_xboole_0 | ~r2_hidden(A_153, A_154))), inference(superposition, [status(thm), theory('equality')], [c_100, c_426])).
% 5.14/1.90  tff(c_460, plain, (![C_155, A_156]: (k11_relat_1(k1_xboole_0, C_155)=k1_xboole_0 | ~r1_tarski(C_155, A_156))), inference(resolution, [status(thm)], [c_78, c_447])).
% 5.14/1.90  tff(c_472, plain, (![B_3]: (k11_relat_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_460])).
% 5.14/1.90  tff(c_142, plain, (![A_96]: (k1_relat_1('#skF_10'(A_96))=A_96)), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.14/1.90  tff(c_146, plain, (![A_96]: (v1_relat_1('#skF_10'(A_96)))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.14/1.90  tff(c_295, plain, (![A_96]: (k1_relat_1('#skF_10'(A_96))!=k1_xboole_0 | '#skF_10'(A_96)=k1_xboole_0)), inference(resolution, [status(thm)], [c_146, c_286])).
% 5.14/1.90  tff(c_301, plain, (![A_96]: (k1_xboole_0!=A_96 | '#skF_10'(A_96)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_142, c_295])).
% 5.14/1.90  tff(c_713, plain, (![B_183, A_184]: (k11_relat_1(B_183, A_184)!=k1_xboole_0 | ~r2_hidden(A_184, k1_relat_1(B_183)) | ~v1_relat_1(B_183))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.14/1.90  tff(c_730, plain, (![A_96, A_184]: (k11_relat_1('#skF_10'(A_96), A_184)!=k1_xboole_0 | ~r2_hidden(A_184, A_96) | ~v1_relat_1('#skF_10'(A_96)))), inference(superposition, [status(thm), theory('equality')], [c_142, c_713])).
% 5.14/1.90  tff(c_741, plain, (![A_185, A_186]: (k11_relat_1('#skF_10'(A_185), A_186)!=k1_xboole_0 | ~r2_hidden(A_186, A_185))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_730])).
% 5.14/1.90  tff(c_747, plain, (![A_186, A_96]: (k11_relat_1(k1_xboole_0, A_186)!=k1_xboole_0 | ~r2_hidden(A_186, A_96) | k1_xboole_0!=A_96)), inference(superposition, [status(thm), theory('equality')], [c_301, c_741])).
% 5.14/1.90  tff(c_752, plain, (![A_187, A_188]: (~r2_hidden(A_187, A_188) | k1_xboole_0!=A_188)), inference(demodulation, [status(thm), theory('equality')], [c_472, c_747])).
% 5.14/1.90  tff(c_821, plain, (![A_194, C_195]: (k1_zfmisc_1(A_194)!=k1_xboole_0 | ~r1_tarski(C_195, A_194))), inference(resolution, [status(thm)], [c_78, c_752])).
% 5.14/1.90  tff(c_836, plain, (![A_83]: (k1_zfmisc_1(A_83)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_316, c_821])).
% 5.14/1.90  tff(c_148, plain, (![A_102]: (k9_setfam_1(A_102)=k1_zfmisc_1(A_102))), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.14/1.90  tff(c_154, plain, (![A_105]: (k2_yellow_1(k9_setfam_1(A_105))=k3_yellow_1(A_105))), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.14/1.90  tff(c_157, plain, (![A_105]: (k2_yellow_1(k1_zfmisc_1(A_105))=k3_yellow_1(A_105))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_154])).
% 5.14/1.90  tff(c_488, plain, (![A_158]: (k3_yellow_0(k2_yellow_1(A_158))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_158) | v1_xboole_0(A_158))), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.14/1.90  tff(c_3602, plain, (![A_6946]: (k3_yellow_0(k3_yellow_1(A_6946))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_6946)) | v1_xboole_0(k1_zfmisc_1(A_6946)))), inference(superposition, [status(thm), theory('equality')], [c_157, c_488])).
% 5.14/1.90  tff(c_3629, plain, (![A_18]: (k3_yellow_0(k3_yellow_1(A_18))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_18)) | ~r1_tarski(k1_xboole_0, A_18))), inference(resolution, [status(thm)], [c_78, c_3602])).
% 5.14/1.90  tff(c_3634, plain, (![A_7011]: (k3_yellow_0(k3_yellow_1(A_7011))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_7011)))), inference(demodulation, [status(thm), theory('equality')], [c_316, c_3629])).
% 5.14/1.90  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.14/1.90  tff(c_3637, plain, (![A_7011]: (k1_zfmisc_1(A_7011)=k1_xboole_0 | k3_yellow_0(k3_yellow_1(A_7011))=k1_xboole_0)), inference(resolution, [status(thm)], [c_3634, c_2])).
% 5.14/1.90  tff(c_3679, plain, (![A_7011]: (k3_yellow_0(k3_yellow_1(A_7011))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_836, c_3637])).
% 5.14/1.90  tff(c_156, plain, (k3_yellow_0(k3_yellow_1('#skF_11'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.14/1.90  tff(c_3685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3679, c_156])).
% 5.14/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.14/1.90  
% 5.14/1.90  Inference rules
% 5.14/1.90  ----------------------
% 5.14/1.90  #Ref     : 0
% 5.14/1.90  #Sup     : 755
% 5.14/1.90  #Fact    : 0
% 5.14/1.90  #Define  : 0
% 5.14/1.90  #Split   : 3
% 5.14/1.90  #Chain   : 0
% 5.14/1.90  #Close   : 0
% 5.14/1.90  
% 5.14/1.90  Ordering : KBO
% 5.14/1.90  
% 5.14/1.90  Simplification rules
% 5.14/1.90  ----------------------
% 5.14/1.90  #Subsume      : 271
% 5.14/1.90  #Demod        : 373
% 5.14/1.90  #Tautology    : 357
% 5.14/1.90  #SimpNegUnit  : 15
% 5.14/1.90  #BackRed      : 8
% 5.14/1.90  
% 5.14/1.90  #Partial instantiations: 1664
% 5.14/1.90  #Strategies tried      : 1
% 5.14/1.90  
% 5.14/1.90  Timing (in seconds)
% 5.14/1.90  ----------------------
% 5.14/1.90  Preprocessing        : 0.38
% 5.14/1.90  Parsing              : 0.18
% 5.14/1.90  CNF conversion       : 0.03
% 5.14/1.90  Main loop            : 0.76
% 5.14/1.90  Inferencing          : 0.28
% 5.14/1.90  Reduction            : 0.21
% 5.14/1.90  Demodulation         : 0.15
% 5.14/1.90  BG Simplification    : 0.04
% 5.14/1.90  Subsumption          : 0.19
% 5.14/1.90  Abstraction          : 0.05
% 5.14/1.90  MUC search           : 0.00
% 5.14/1.90  Cooper               : 0.00
% 5.14/1.90  Total                : 1.17
% 5.14/1.90  Index Insertion      : 0.00
% 5.14/1.90  Index Deletion       : 0.00
% 5.14/1.90  Index Matching       : 0.00
% 5.14/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
