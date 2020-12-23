%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:04 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 243 expanded)
%              Number of leaves         :   31 (  95 expanded)
%              Depth                    :   12
%              Number of atoms          :  114 ( 610 expanded)
%              Number of equality atoms :   82 ( 414 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(np__1,type,(
    np__1: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_58,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(c_24,plain,(
    ! [A_14] : v1_funct_1('#skF_1'(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    ! [A_14] : k1_relat_1('#skF_1'(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    ! [A_14] : v1_relat_1('#skF_1'(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    ! [A_20,B_24] :
      ( k1_relat_1('#skF_2'(A_20,B_24)) = A_20
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,(
    ! [A_20,B_24] :
      ( v1_funct_1('#skF_2'(A_20,B_24))
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_83,plain,(
    ! [A_43,B_44] :
      ( v1_relat_1('#skF_2'(A_43,B_44))
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_38,plain,(
    ! [C_31,B_29] :
      ( C_31 = B_29
      | k1_relat_1(C_31) != '#skF_3'
      | k1_relat_1(B_29) != '#skF_3'
      | ~ v1_funct_1(C_31)
      | ~ v1_relat_1(C_31)
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_156,plain,(
    ! [B_59,A_60,B_61] :
      ( B_59 = '#skF_2'(A_60,B_61)
      | k1_relat_1('#skF_2'(A_60,B_61)) != '#skF_3'
      | k1_relat_1(B_59) != '#skF_3'
      | ~ v1_funct_1('#skF_2'(A_60,B_61))
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59)
      | k1_xboole_0 = A_60 ) ),
    inference(resolution,[status(thm)],[c_83,c_38])).

tff(c_271,plain,(
    ! [B_74,A_75,B_76] :
      ( B_74 = '#skF_2'(A_75,B_76)
      | k1_relat_1('#skF_2'(A_75,B_76)) != '#skF_3'
      | k1_relat_1(B_74) != '#skF_3'
      | ~ v1_funct_1(B_74)
      | ~ v1_relat_1(B_74)
      | k1_xboole_0 = A_75 ) ),
    inference(resolution,[status(thm)],[c_32,c_156])).

tff(c_443,plain,(
    ! [B_95,A_96,B_97] :
      ( B_95 = '#skF_2'(A_96,B_97)
      | A_96 != '#skF_3'
      | k1_relat_1(B_95) != '#skF_3'
      | ~ v1_funct_1(B_95)
      | ~ v1_relat_1(B_95)
      | k1_xboole_0 = A_96
      | k1_xboole_0 = A_96 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_271])).

tff(c_447,plain,(
    ! [A_96,B_97,A_14] :
      ( '#skF_2'(A_96,B_97) = '#skF_1'(A_14)
      | A_96 != '#skF_3'
      | k1_relat_1('#skF_1'(A_14)) != '#skF_3'
      | ~ v1_funct_1('#skF_1'(A_14))
      | k1_xboole_0 = A_96 ) ),
    inference(resolution,[status(thm)],[c_26,c_443])).

tff(c_454,plain,(
    ! [A_98,B_99,A_100] :
      ( '#skF_2'(A_98,B_99) = '#skF_1'(A_100)
      | A_98 != '#skF_3'
      | A_100 != '#skF_3'
      | k1_xboole_0 = A_98 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_447])).

tff(c_28,plain,(
    ! [A_20,B_24] :
      ( k2_relat_1('#skF_2'(A_20,B_24)) = k1_tarski(B_24)
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_476,plain,(
    ! [A_100,B_99,A_98] :
      ( k2_relat_1('#skF_1'(A_100)) = k1_tarski(B_99)
      | k1_xboole_0 = A_98
      | A_98 != '#skF_3'
      | A_100 != '#skF_3'
      | k1_xboole_0 = A_98 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_28])).

tff(c_575,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_476])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_592,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_36])).

tff(c_595,plain,(
    ! [A_108,B_109] :
      ( k2_relat_1('#skF_1'(A_108)) = k1_tarski(B_109)
      | A_108 != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_476])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_160,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k4_xboole_0(A_62,B_63)) = k3_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_175,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_160])).

tff(c_180,plain,(
    ! [A_64] : k4_xboole_0(A_64,A_64) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_175])).

tff(c_6,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_185,plain,(
    ! [A_64] : k4_xboole_0(A_64,k1_xboole_0) = k3_xboole_0(A_64,A_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_6])).

tff(c_197,plain,(
    ! [A_64] : k3_xboole_0(A_64,A_64) = A_64 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_185])).

tff(c_12,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_87,plain,(
    ! [A_45,B_46] : k1_setfam_1(k2_tarski(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_96,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = k1_setfam_1(k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_87])).

tff(c_202,plain,(
    ! [A_7] : k1_setfam_1(k1_tarski(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_96])).

tff(c_682,plain,(
    ! [A_115] :
      ( k1_setfam_1(k2_relat_1('#skF_1'(A_115))) = k1_xboole_0
      | A_115 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_202])).

tff(c_603,plain,(
    ! [A_108,B_109] :
      ( k1_setfam_1(k2_relat_1('#skF_1'(A_108))) = B_109
      | A_108 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_202])).

tff(c_685,plain,(
    ! [B_109,A_115] :
      ( k1_xboole_0 = B_109
      | A_115 != '#skF_3'
      | A_115 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_682,c_603])).

tff(c_941,plain,(
    ! [A_115] :
      ( A_115 != '#skF_3'
      | A_115 != '#skF_3' ) ),
    inference(splitLeft,[status(thm)],[c_685])).

tff(c_947,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_941])).

tff(c_949,plain,(
    ! [B_870] : k1_xboole_0 = B_870 ),
    inference(splitRight,[status(thm)],[c_685])).

tff(c_178,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_175])).

tff(c_125,plain,(
    ! [A_50,B_51] :
      ( r1_xboole_0(A_50,B_51)
      | k4_xboole_0(A_50,B_51) != A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [B_11] : ~ r1_xboole_0(k1_tarski(B_11),k1_tarski(B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_129,plain,(
    ! [B_11] : k4_xboole_0(k1_tarski(B_11),k1_tarski(B_11)) != k1_tarski(B_11) ),
    inference(resolution,[status(thm)],[c_125,c_16])).

tff(c_179,plain,(
    ! [B_11] : k1_tarski(B_11) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_129])).

tff(c_1033,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_949,c_179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 15:55:07 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.46  
% 2.88/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.46  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.88/1.46  
% 2.88/1.46  %Foreground sorts:
% 2.88/1.46  
% 2.88/1.46  
% 2.88/1.46  %Background operators:
% 2.88/1.46  
% 2.88/1.46  
% 2.88/1.46  %Foreground operators:
% 2.88/1.46  tff(np__1, type, np__1: $i).
% 2.88/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.88/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.88/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.88/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.88/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.88/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.88/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.88/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.88/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.88/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.88/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.88/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.88/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.88/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.88/1.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.88/1.46  
% 3.21/1.47  tff(f_58, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 3.21/1.47  tff(f_71, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 3.21/1.47  tff(f_90, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 3.21/1.47  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.21/1.47  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.21/1.47  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.21/1.47  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.21/1.47  tff(f_46, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.21/1.47  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.21/1.47  tff(f_44, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 3.21/1.47  tff(c_24, plain, (![A_14]: (v1_funct_1('#skF_1'(A_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.21/1.47  tff(c_22, plain, (![A_14]: (k1_relat_1('#skF_1'(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.21/1.47  tff(c_26, plain, (![A_14]: (v1_relat_1('#skF_1'(A_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.21/1.47  tff(c_30, plain, (![A_20, B_24]: (k1_relat_1('#skF_2'(A_20, B_24))=A_20 | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.21/1.47  tff(c_32, plain, (![A_20, B_24]: (v1_funct_1('#skF_2'(A_20, B_24)) | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.21/1.47  tff(c_83, plain, (![A_43, B_44]: (v1_relat_1('#skF_2'(A_43, B_44)) | k1_xboole_0=A_43)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.21/1.47  tff(c_38, plain, (![C_31, B_29]: (C_31=B_29 | k1_relat_1(C_31)!='#skF_3' | k1_relat_1(B_29)!='#skF_3' | ~v1_funct_1(C_31) | ~v1_relat_1(C_31) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.47  tff(c_156, plain, (![B_59, A_60, B_61]: (B_59='#skF_2'(A_60, B_61) | k1_relat_1('#skF_2'(A_60, B_61))!='#skF_3' | k1_relat_1(B_59)!='#skF_3' | ~v1_funct_1('#skF_2'(A_60, B_61)) | ~v1_funct_1(B_59) | ~v1_relat_1(B_59) | k1_xboole_0=A_60)), inference(resolution, [status(thm)], [c_83, c_38])).
% 3.21/1.47  tff(c_271, plain, (![B_74, A_75, B_76]: (B_74='#skF_2'(A_75, B_76) | k1_relat_1('#skF_2'(A_75, B_76))!='#skF_3' | k1_relat_1(B_74)!='#skF_3' | ~v1_funct_1(B_74) | ~v1_relat_1(B_74) | k1_xboole_0=A_75)), inference(resolution, [status(thm)], [c_32, c_156])).
% 3.21/1.47  tff(c_443, plain, (![B_95, A_96, B_97]: (B_95='#skF_2'(A_96, B_97) | A_96!='#skF_3' | k1_relat_1(B_95)!='#skF_3' | ~v1_funct_1(B_95) | ~v1_relat_1(B_95) | k1_xboole_0=A_96 | k1_xboole_0=A_96)), inference(superposition, [status(thm), theory('equality')], [c_30, c_271])).
% 3.21/1.47  tff(c_447, plain, (![A_96, B_97, A_14]: ('#skF_2'(A_96, B_97)='#skF_1'(A_14) | A_96!='#skF_3' | k1_relat_1('#skF_1'(A_14))!='#skF_3' | ~v1_funct_1('#skF_1'(A_14)) | k1_xboole_0=A_96)), inference(resolution, [status(thm)], [c_26, c_443])).
% 3.21/1.47  tff(c_454, plain, (![A_98, B_99, A_100]: ('#skF_2'(A_98, B_99)='#skF_1'(A_100) | A_98!='#skF_3' | A_100!='#skF_3' | k1_xboole_0=A_98)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_447])).
% 3.21/1.47  tff(c_28, plain, (![A_20, B_24]: (k2_relat_1('#skF_2'(A_20, B_24))=k1_tarski(B_24) | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.21/1.47  tff(c_476, plain, (![A_100, B_99, A_98]: (k2_relat_1('#skF_1'(A_100))=k1_tarski(B_99) | k1_xboole_0=A_98 | A_98!='#skF_3' | A_100!='#skF_3' | k1_xboole_0=A_98)), inference(superposition, [status(thm), theory('equality')], [c_454, c_28])).
% 3.21/1.47  tff(c_575, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_476])).
% 3.21/1.47  tff(c_36, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.47  tff(c_592, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_575, c_36])).
% 3.21/1.47  tff(c_595, plain, (![A_108, B_109]: (k2_relat_1('#skF_1'(A_108))=k1_tarski(B_109) | A_108!='#skF_3')), inference(splitRight, [status(thm)], [c_476])).
% 3.21/1.47  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.21/1.47  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.21/1.47  tff(c_160, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k4_xboole_0(A_62, B_63))=k3_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.47  tff(c_175, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_160])).
% 3.21/1.47  tff(c_180, plain, (![A_64]: (k4_xboole_0(A_64, A_64)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_175])).
% 3.21/1.47  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.47  tff(c_185, plain, (![A_64]: (k4_xboole_0(A_64, k1_xboole_0)=k3_xboole_0(A_64, A_64))), inference(superposition, [status(thm), theory('equality')], [c_180, c_6])).
% 3.21/1.47  tff(c_197, plain, (![A_64]: (k3_xboole_0(A_64, A_64)=A_64)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_185])).
% 3.21/1.47  tff(c_12, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.21/1.47  tff(c_87, plain, (![A_45, B_46]: (k1_setfam_1(k2_tarski(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.21/1.47  tff(c_96, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=k1_setfam_1(k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_87])).
% 3.21/1.47  tff(c_202, plain, (![A_7]: (k1_setfam_1(k1_tarski(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_197, c_96])).
% 3.21/1.47  tff(c_682, plain, (![A_115]: (k1_setfam_1(k2_relat_1('#skF_1'(A_115)))=k1_xboole_0 | A_115!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_595, c_202])).
% 3.21/1.47  tff(c_603, plain, (![A_108, B_109]: (k1_setfam_1(k2_relat_1('#skF_1'(A_108)))=B_109 | A_108!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_595, c_202])).
% 3.21/1.47  tff(c_685, plain, (![B_109, A_115]: (k1_xboole_0=B_109 | A_115!='#skF_3' | A_115!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_682, c_603])).
% 3.21/1.47  tff(c_941, plain, (![A_115]: (A_115!='#skF_3' | A_115!='#skF_3')), inference(splitLeft, [status(thm)], [c_685])).
% 3.21/1.47  tff(c_947, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_941])).
% 3.21/1.47  tff(c_949, plain, (![B_870]: (k1_xboole_0=B_870)), inference(splitRight, [status(thm)], [c_685])).
% 3.21/1.47  tff(c_178, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_175])).
% 3.21/1.47  tff(c_125, plain, (![A_50, B_51]: (r1_xboole_0(A_50, B_51) | k4_xboole_0(A_50, B_51)!=A_50)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.47  tff(c_16, plain, (![B_11]: (~r1_xboole_0(k1_tarski(B_11), k1_tarski(B_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.21/1.47  tff(c_129, plain, (![B_11]: (k4_xboole_0(k1_tarski(B_11), k1_tarski(B_11))!=k1_tarski(B_11))), inference(resolution, [status(thm)], [c_125, c_16])).
% 3.21/1.47  tff(c_179, plain, (![B_11]: (k1_tarski(B_11)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_178, c_129])).
% 3.21/1.47  tff(c_1033, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_949, c_179])).
% 3.21/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.47  
% 3.21/1.47  Inference rules
% 3.21/1.47  ----------------------
% 3.21/1.47  #Ref     : 3
% 3.21/1.47  #Sup     : 275
% 3.21/1.47  #Fact    : 0
% 3.21/1.47  #Define  : 0
% 3.21/1.47  #Split   : 2
% 3.21/1.47  #Chain   : 0
% 3.21/1.47  #Close   : 0
% 3.21/1.47  
% 3.21/1.47  Ordering : KBO
% 3.21/1.47  
% 3.21/1.47  Simplification rules
% 3.21/1.47  ----------------------
% 3.21/1.47  #Subsume      : 90
% 3.21/1.47  #Demod        : 78
% 3.21/1.47  #Tautology    : 70
% 3.21/1.47  #SimpNegUnit  : 1
% 3.21/1.47  #BackRed      : 13
% 3.21/1.47  
% 3.21/1.47  #Partial instantiations: 602
% 3.21/1.47  #Strategies tried      : 1
% 3.21/1.47  
% 3.21/1.47  Timing (in seconds)
% 3.21/1.47  ----------------------
% 3.21/1.48  Preprocessing        : 0.31
% 3.21/1.48  Parsing              : 0.17
% 3.21/1.48  CNF conversion       : 0.02
% 3.21/1.48  Main loop            : 0.40
% 3.21/1.48  Inferencing          : 0.16
% 3.21/1.48  Reduction            : 0.11
% 3.21/1.48  Demodulation         : 0.08
% 3.21/1.48  BG Simplification    : 0.02
% 3.21/1.48  Subsumption          : 0.08
% 3.21/1.48  Abstraction          : 0.02
% 3.21/1.48  MUC search           : 0.00
% 3.21/1.48  Cooper               : 0.00
% 3.21/1.48  Total                : 0.74
% 3.21/1.48  Index Insertion      : 0.00
% 3.21/1.48  Index Deletion       : 0.00
% 3.21/1.48  Index Matching       : 0.00
% 3.21/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
