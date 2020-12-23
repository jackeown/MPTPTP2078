%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:31 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 125 expanded)
%              Number of leaves         :   43 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 172 expanded)
%              Number of equality atoms :   42 (  70 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k3_tarski > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_89,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_111,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_113,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_115,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_58,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_64,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_60,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_38,plain,(
    ! [A_49] : k1_relat_1(k6_relat_1(A_49)) = A_49 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_44,plain,(
    ! [A_52] : v1_relat_1(k6_relat_1(A_52)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_159,plain,(
    ! [A_92,B_93] :
      ( k5_relat_1(k6_relat_1(A_92),B_93) = k7_relat_1(B_93,A_92)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_52,plain,(
    ! [B_59,A_58] : k5_relat_1(k6_relat_1(B_59),k6_relat_1(A_58)) = k6_relat_1(k3_xboole_0(A_58,B_59)) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_166,plain,(
    ! [A_58,A_92] :
      ( k7_relat_1(k6_relat_1(A_58),A_92) = k6_relat_1(k3_xboole_0(A_58,A_92))
      | ~ v1_relat_1(k6_relat_1(A_58)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_52])).

tff(c_175,plain,(
    ! [A_58,A_92] : k7_relat_1(k6_relat_1(A_58),A_92) = k6_relat_1(k3_xboole_0(A_58,A_92)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_166])).

tff(c_203,plain,(
    ! [B_98,A_99] :
      ( v4_relat_1(B_98,A_99)
      | ~ r1_tarski(k1_relat_1(B_98),A_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_213,plain,(
    ! [A_49,A_99] :
      ( v4_relat_1(k6_relat_1(A_49),A_99)
      | ~ r1_tarski(A_49,A_99)
      | ~ v1_relat_1(k6_relat_1(A_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_203])).

tff(c_218,plain,(
    ! [A_100,A_101] :
      ( v4_relat_1(k6_relat_1(A_100),A_101)
      | ~ r1_tarski(A_100,A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_213])).

tff(c_34,plain,(
    ! [B_44,A_43] :
      ( k7_relat_1(B_44,A_43) = B_44
      | ~ v4_relat_1(B_44,A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_226,plain,(
    ! [A_100,A_101] :
      ( k7_relat_1(k6_relat_1(A_100),A_101) = k6_relat_1(A_100)
      | ~ v1_relat_1(k6_relat_1(A_100))
      | ~ r1_tarski(A_100,A_101) ) ),
    inference(resolution,[status(thm)],[c_218,c_34])).

tff(c_351,plain,(
    ! [A_111,A_112] :
      ( k6_relat_1(k3_xboole_0(A_111,A_112)) = k6_relat_1(A_111)
      | ~ r1_tarski(A_111,A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_175,c_226])).

tff(c_387,plain,(
    ! [A_111,A_112] :
      ( k3_xboole_0(A_111,A_112) = k1_relat_1(k6_relat_1(A_111))
      | ~ r1_tarski(A_111,A_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_38])).

tff(c_535,plain,(
    ! [A_129,A_130] :
      ( k3_xboole_0(A_129,A_130) = A_129
      | ~ r1_tarski(A_129,A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_387])).

tff(c_555,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_535])).

tff(c_46,plain,(
    ! [A_52] : v1_funct_1(k6_relat_1(A_52)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_54,plain,(
    ! [A_60] : v2_funct_1(k6_relat_1(A_60)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_42,plain,(
    ! [A_50,B_51] :
      ( k5_relat_1(k6_relat_1(A_50),B_51) = k7_relat_1(B_51,A_50)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1000,plain,(
    ! [A_158,B_159] :
      ( k10_relat_1(A_158,k1_relat_1(B_159)) = k1_relat_1(k5_relat_1(A_158,B_159))
      | ~ v1_relat_1(B_159)
      | ~ v1_relat_1(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1012,plain,(
    ! [A_158,A_49] :
      ( k1_relat_1(k5_relat_1(A_158,k6_relat_1(A_49))) = k10_relat_1(A_158,A_49)
      | ~ v1_relat_1(k6_relat_1(A_49))
      | ~ v1_relat_1(A_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1000])).

tff(c_1259,plain,(
    ! [A_166,A_167] :
      ( k1_relat_1(k5_relat_1(A_166,k6_relat_1(A_167))) = k10_relat_1(A_166,A_167)
      | ~ v1_relat_1(A_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1012])).

tff(c_1293,plain,(
    ! [A_167,A_50] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_167),A_50)) = k10_relat_1(k6_relat_1(A_50),A_167)
      | ~ v1_relat_1(k6_relat_1(A_50))
      | ~ v1_relat_1(k6_relat_1(A_167)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1259])).

tff(c_1300,plain,(
    ! [A_50,A_167] : k10_relat_1(k6_relat_1(A_50),A_167) = k3_xboole_0(A_167,A_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_38,c_175,c_1293])).

tff(c_40,plain,(
    ! [A_49] : k2_relat_1(k6_relat_1(A_49)) = A_49 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_179,plain,(
    ! [A_94,A_95] : k7_relat_1(k6_relat_1(A_94),A_95) = k6_relat_1(k3_xboole_0(A_94,A_95)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_166])).

tff(c_30,plain,(
    ! [B_39,A_38] :
      ( k2_relat_1(k7_relat_1(B_39,A_38)) = k9_relat_1(B_39,A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_185,plain,(
    ! [A_94,A_95] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_94,A_95))) = k9_relat_1(k6_relat_1(A_94),A_95)
      | ~ v1_relat_1(k6_relat_1(A_94)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_30])).

tff(c_191,plain,(
    ! [A_94,A_95] : k9_relat_1(k6_relat_1(A_94),A_95) = k3_xboole_0(A_94,A_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_185])).

tff(c_56,plain,(
    ! [A_61] : k2_funct_1(k6_relat_1(A_61)) = k6_relat_1(A_61) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1365,plain,(
    ! [B_173,A_174] :
      ( k9_relat_1(k2_funct_1(B_173),A_174) = k10_relat_1(B_173,A_174)
      | ~ v2_funct_1(B_173)
      | ~ v1_funct_1(B_173)
      | ~ v1_relat_1(B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1374,plain,(
    ! [A_61,A_174] :
      ( k9_relat_1(k6_relat_1(A_61),A_174) = k10_relat_1(k6_relat_1(A_61),A_174)
      | ~ v2_funct_1(k6_relat_1(A_61))
      | ~ v1_funct_1(k6_relat_1(A_61))
      | ~ v1_relat_1(k6_relat_1(A_61)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1365])).

tff(c_1379,plain,(
    ! [A_176,A_175] : k3_xboole_0(A_176,A_175) = k3_xboole_0(A_175,A_176) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_54,c_1300,c_191,c_1374])).

tff(c_1511,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_1379])).

tff(c_48,plain,(
    ! [A_53,C_55,B_54] :
      ( k3_xboole_0(A_53,k10_relat_1(C_55,B_54)) = k10_relat_1(k7_relat_1(C_55,A_53),B_54)
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1823,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1511,c_48])).

tff(c_1846,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1823])).

tff(c_1848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1846])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.61/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.58  
% 3.61/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.58  %$ v4_relat_1 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k3_tarski > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.61/1.58  
% 3.61/1.58  %Foreground sorts:
% 3.61/1.58  
% 3.61/1.58  
% 3.61/1.58  %Background operators:
% 3.61/1.58  
% 3.61/1.58  
% 3.61/1.58  %Foreground operators:
% 3.61/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.61/1.58  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.61/1.58  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.61/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.61/1.58  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.61/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.61/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.61/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.61/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.61/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.61/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.61/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.61/1.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.61/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.61/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.61/1.58  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.61/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.61/1.58  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.61/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.58  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.61/1.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.61/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.61/1.58  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.61/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.61/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.61/1.58  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.61/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.61/1.58  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.61/1.58  
% 3.61/1.59  tff(f_125, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 3.61/1.59  tff(f_89, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.61/1.59  tff(f_97, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.61/1.59  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.61/1.59  tff(f_111, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 3.61/1.59  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.61/1.59  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.61/1.59  tff(f_113, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 3.61/1.59  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.61/1.59  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.61/1.59  tff(f_115, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 3.61/1.59  tff(f_109, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 3.61/1.59  tff(f_101, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 3.61/1.59  tff(c_58, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.61/1.59  tff(c_64, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.61/1.59  tff(c_60, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.61/1.59  tff(c_38, plain, (![A_49]: (k1_relat_1(k6_relat_1(A_49))=A_49)), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.61/1.59  tff(c_44, plain, (![A_52]: (v1_relat_1(k6_relat_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.61/1.59  tff(c_159, plain, (![A_92, B_93]: (k5_relat_1(k6_relat_1(A_92), B_93)=k7_relat_1(B_93, A_92) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.61/1.59  tff(c_52, plain, (![B_59, A_58]: (k5_relat_1(k6_relat_1(B_59), k6_relat_1(A_58))=k6_relat_1(k3_xboole_0(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.61/1.59  tff(c_166, plain, (![A_58, A_92]: (k7_relat_1(k6_relat_1(A_58), A_92)=k6_relat_1(k3_xboole_0(A_58, A_92)) | ~v1_relat_1(k6_relat_1(A_58)))), inference(superposition, [status(thm), theory('equality')], [c_159, c_52])).
% 3.61/1.59  tff(c_175, plain, (![A_58, A_92]: (k7_relat_1(k6_relat_1(A_58), A_92)=k6_relat_1(k3_xboole_0(A_58, A_92)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_166])).
% 3.61/1.59  tff(c_203, plain, (![B_98, A_99]: (v4_relat_1(B_98, A_99) | ~r1_tarski(k1_relat_1(B_98), A_99) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.61/1.59  tff(c_213, plain, (![A_49, A_99]: (v4_relat_1(k6_relat_1(A_49), A_99) | ~r1_tarski(A_49, A_99) | ~v1_relat_1(k6_relat_1(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_203])).
% 3.61/1.59  tff(c_218, plain, (![A_100, A_101]: (v4_relat_1(k6_relat_1(A_100), A_101) | ~r1_tarski(A_100, A_101))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_213])).
% 3.61/1.59  tff(c_34, plain, (![B_44, A_43]: (k7_relat_1(B_44, A_43)=B_44 | ~v4_relat_1(B_44, A_43) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.61/1.59  tff(c_226, plain, (![A_100, A_101]: (k7_relat_1(k6_relat_1(A_100), A_101)=k6_relat_1(A_100) | ~v1_relat_1(k6_relat_1(A_100)) | ~r1_tarski(A_100, A_101))), inference(resolution, [status(thm)], [c_218, c_34])).
% 3.61/1.59  tff(c_351, plain, (![A_111, A_112]: (k6_relat_1(k3_xboole_0(A_111, A_112))=k6_relat_1(A_111) | ~r1_tarski(A_111, A_112))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_175, c_226])).
% 3.61/1.59  tff(c_387, plain, (![A_111, A_112]: (k3_xboole_0(A_111, A_112)=k1_relat_1(k6_relat_1(A_111)) | ~r1_tarski(A_111, A_112))), inference(superposition, [status(thm), theory('equality')], [c_351, c_38])).
% 3.61/1.59  tff(c_535, plain, (![A_129, A_130]: (k3_xboole_0(A_129, A_130)=A_129 | ~r1_tarski(A_129, A_130))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_387])).
% 3.61/1.59  tff(c_555, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_535])).
% 3.61/1.59  tff(c_46, plain, (![A_52]: (v1_funct_1(k6_relat_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.61/1.59  tff(c_54, plain, (![A_60]: (v2_funct_1(k6_relat_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.61/1.59  tff(c_42, plain, (![A_50, B_51]: (k5_relat_1(k6_relat_1(A_50), B_51)=k7_relat_1(B_51, A_50) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.61/1.59  tff(c_1000, plain, (![A_158, B_159]: (k10_relat_1(A_158, k1_relat_1(B_159))=k1_relat_1(k5_relat_1(A_158, B_159)) | ~v1_relat_1(B_159) | ~v1_relat_1(A_158))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.61/1.59  tff(c_1012, plain, (![A_158, A_49]: (k1_relat_1(k5_relat_1(A_158, k6_relat_1(A_49)))=k10_relat_1(A_158, A_49) | ~v1_relat_1(k6_relat_1(A_49)) | ~v1_relat_1(A_158))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1000])).
% 3.61/1.59  tff(c_1259, plain, (![A_166, A_167]: (k1_relat_1(k5_relat_1(A_166, k6_relat_1(A_167)))=k10_relat_1(A_166, A_167) | ~v1_relat_1(A_166))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1012])).
% 3.61/1.59  tff(c_1293, plain, (![A_167, A_50]: (k1_relat_1(k7_relat_1(k6_relat_1(A_167), A_50))=k10_relat_1(k6_relat_1(A_50), A_167) | ~v1_relat_1(k6_relat_1(A_50)) | ~v1_relat_1(k6_relat_1(A_167)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1259])).
% 3.61/1.59  tff(c_1300, plain, (![A_50, A_167]: (k10_relat_1(k6_relat_1(A_50), A_167)=k3_xboole_0(A_167, A_50))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_38, c_175, c_1293])).
% 3.61/1.59  tff(c_40, plain, (![A_49]: (k2_relat_1(k6_relat_1(A_49))=A_49)), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.61/1.59  tff(c_179, plain, (![A_94, A_95]: (k7_relat_1(k6_relat_1(A_94), A_95)=k6_relat_1(k3_xboole_0(A_94, A_95)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_166])).
% 3.61/1.59  tff(c_30, plain, (![B_39, A_38]: (k2_relat_1(k7_relat_1(B_39, A_38))=k9_relat_1(B_39, A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.61/1.59  tff(c_185, plain, (![A_94, A_95]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_94, A_95)))=k9_relat_1(k6_relat_1(A_94), A_95) | ~v1_relat_1(k6_relat_1(A_94)))), inference(superposition, [status(thm), theory('equality')], [c_179, c_30])).
% 3.61/1.59  tff(c_191, plain, (![A_94, A_95]: (k9_relat_1(k6_relat_1(A_94), A_95)=k3_xboole_0(A_94, A_95))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_185])).
% 3.61/1.59  tff(c_56, plain, (![A_61]: (k2_funct_1(k6_relat_1(A_61))=k6_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.61/1.59  tff(c_1365, plain, (![B_173, A_174]: (k9_relat_1(k2_funct_1(B_173), A_174)=k10_relat_1(B_173, A_174) | ~v2_funct_1(B_173) | ~v1_funct_1(B_173) | ~v1_relat_1(B_173))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.61/1.59  tff(c_1374, plain, (![A_61, A_174]: (k9_relat_1(k6_relat_1(A_61), A_174)=k10_relat_1(k6_relat_1(A_61), A_174) | ~v2_funct_1(k6_relat_1(A_61)) | ~v1_funct_1(k6_relat_1(A_61)) | ~v1_relat_1(k6_relat_1(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1365])).
% 3.61/1.59  tff(c_1379, plain, (![A_176, A_175]: (k3_xboole_0(A_176, A_175)=k3_xboole_0(A_175, A_176))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_54, c_1300, c_191, c_1374])).
% 3.61/1.59  tff(c_1511, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_555, c_1379])).
% 3.61/1.59  tff(c_48, plain, (![A_53, C_55, B_54]: (k3_xboole_0(A_53, k10_relat_1(C_55, B_54))=k10_relat_1(k7_relat_1(C_55, A_53), B_54) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.61/1.59  tff(c_1823, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1511, c_48])).
% 3.61/1.59  tff(c_1846, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1823])).
% 3.61/1.59  tff(c_1848, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1846])).
% 3.61/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.59  
% 3.61/1.59  Inference rules
% 3.61/1.59  ----------------------
% 3.61/1.59  #Ref     : 0
% 3.61/1.59  #Sup     : 421
% 3.61/1.59  #Fact    : 0
% 3.61/1.59  #Define  : 0
% 3.61/1.59  #Split   : 0
% 3.61/1.59  #Chain   : 0
% 3.61/1.59  #Close   : 0
% 3.61/1.59  
% 3.61/1.59  Ordering : KBO
% 3.61/1.59  
% 3.61/1.59  Simplification rules
% 3.61/1.59  ----------------------
% 3.61/1.59  #Subsume      : 23
% 3.61/1.59  #Demod        : 248
% 3.61/1.59  #Tautology    : 208
% 3.61/1.59  #SimpNegUnit  : 1
% 3.61/1.59  #BackRed      : 0
% 3.61/1.59  
% 3.61/1.59  #Partial instantiations: 0
% 3.61/1.59  #Strategies tried      : 1
% 3.61/1.59  
% 3.61/1.59  Timing (in seconds)
% 3.61/1.59  ----------------------
% 3.61/1.60  Preprocessing        : 0.34
% 3.61/1.60  Parsing              : 0.19
% 3.61/1.60  CNF conversion       : 0.02
% 3.61/1.60  Main loop            : 0.49
% 3.61/1.60  Inferencing          : 0.18
% 3.61/1.60  Reduction            : 0.18
% 3.61/1.60  Demodulation         : 0.14
% 3.61/1.60  BG Simplification    : 0.03
% 3.61/1.60  Subsumption          : 0.08
% 3.61/1.60  Abstraction          : 0.03
% 3.61/1.60  MUC search           : 0.00
% 3.61/1.60  Cooper               : 0.00
% 3.61/1.60  Total                : 0.87
% 3.61/1.60  Index Insertion      : 0.00
% 3.61/1.60  Index Deletion       : 0.00
% 3.61/1.60  Index Matching       : 0.00
% 3.61/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
