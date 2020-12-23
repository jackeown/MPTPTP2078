%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:06 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 273 expanded)
%              Number of leaves         :   48 ( 116 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 496 expanded)
%              Number of equality atoms :   45 ( 158 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_100,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_75,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_63,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_74,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_32,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_30,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_34,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_50,plain,(
    ! [A_49] :
      ( r2_hidden('#skF_1'(A_49),A_49)
      | k1_xboole_0 = A_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_28,plain,(
    ! [B_35] : k2_zfmisc_1(k1_xboole_0,B_35) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_59,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_54])).

tff(c_288,plain,(
    ! [C_93,B_94,A_95] :
      ( ~ v1_xboole_0(C_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(C_93))
      | ~ r2_hidden(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_290,plain,(
    ! [A_95] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_95,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_59,c_288])).

tff(c_294,plain,(
    ! [A_96] : ~ r2_hidden(A_96,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_290])).

tff(c_299,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_294])).

tff(c_44,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_72,plain,(
    ! [A_71] : v1_relat_1(k6_relat_1(A_71)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_74,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_72])).

tff(c_42,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_260,plain,(
    ! [A_89] :
      ( k10_relat_1(A_89,k2_relat_1(A_89)) = k1_relat_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_269,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_260])).

tff(c_273,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_42,c_269])).

tff(c_300,plain,(
    k10_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_299,c_299,c_273])).

tff(c_312,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_74])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_230,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k3_xboole_0(A_86,B_87)) = k4_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_114,plain,(
    ! [B_77,A_78] : k5_xboole_0(B_77,A_78) = k5_xboole_0(A_78,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_130,plain,(
    ! [A_78] : k5_xboole_0(k1_xboole_0,A_78) = A_78 ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_10])).

tff(c_237,plain,(
    ! [B_87] : k4_xboole_0(k1_xboole_0,B_87) = k3_xboole_0(k1_xboole_0,B_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_130])).

tff(c_246,plain,(
    ! [B_87] : k3_xboole_0(k1_xboole_0,B_87) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_237])).

tff(c_301,plain,(
    ! [B_87] : k3_xboole_0('#skF_4',B_87) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_299,c_246])).

tff(c_313,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_299,c_40])).

tff(c_427,plain,(
    ! [B_106,A_107] :
      ( k10_relat_1(B_106,k3_xboole_0(k2_relat_1(B_106),A_107)) = k10_relat_1(B_106,A_107)
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_436,plain,(
    ! [A_107] :
      ( k10_relat_1('#skF_4',k3_xboole_0('#skF_4',A_107)) = k10_relat_1('#skF_4',A_107)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_427])).

tff(c_440,plain,(
    ! [A_107] : k10_relat_1('#skF_4',A_107) = k10_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_301,c_436])).

tff(c_511,plain,(
    ! [A_107] : k10_relat_1('#skF_4',A_107) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_440])).

tff(c_308,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_59])).

tff(c_307,plain,(
    ! [B_35] : k2_zfmisc_1('#skF_4',B_35) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_299,c_28])).

tff(c_506,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( k8_relset_1(A_115,B_116,C_117,D_118) = k10_relat_1(C_117,D_118)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_555,plain,(
    ! [B_122,C_123,D_124] :
      ( k8_relset_1('#skF_4',B_122,C_123,D_124) = k10_relat_1(C_123,D_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_506])).

tff(c_557,plain,(
    ! [B_122,D_124] : k8_relset_1('#skF_4',B_122,'#skF_4',D_124) = k10_relat_1('#skF_4',D_124) ),
    inference(resolution,[status(thm)],[c_308,c_555])).

tff(c_559,plain,(
    ! [B_122,D_124] : k8_relset_1('#skF_4',B_122,'#skF_4',D_124) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_557])).

tff(c_52,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_309,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_299,c_52])).

tff(c_562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_309])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:04:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.37  
% 2.66/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.38  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.66/1.38  
% 2.66/1.38  %Foreground sorts:
% 2.66/1.38  
% 2.66/1.38  
% 2.66/1.38  %Background operators:
% 2.66/1.38  
% 2.66/1.38  
% 2.66/1.38  %Foreground operators:
% 2.66/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.66/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.66/1.38  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.66/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.66/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.66/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.66/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.66/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.66/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.66/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.66/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.66/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.66/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.38  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.38  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.66/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.66/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.66/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.66/1.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.66/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.66/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.66/1.38  
% 2.66/1.39  tff(f_100, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.66/1.39  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.66/1.39  tff(f_52, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.66/1.39  tff(f_109, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 2.66/1.39  tff(f_61, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.66/1.39  tff(f_75, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.66/1.39  tff(f_63, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.66/1.39  tff(f_74, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.66/1.39  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.66/1.39  tff(f_32, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.66/1.39  tff(f_30, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.66/1.39  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.66/1.39  tff(f_34, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.66/1.39  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 2.66/1.39  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.66/1.39  tff(c_50, plain, (![A_49]: (r2_hidden('#skF_1'(A_49), A_49) | k1_xboole_0=A_49)), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.66/1.39  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.66/1.39  tff(c_28, plain, (![B_35]: (k2_zfmisc_1(k1_xboole_0, B_35)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.66/1.39  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.66/1.39  tff(c_59, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_54])).
% 2.66/1.39  tff(c_288, plain, (![C_93, B_94, A_95]: (~v1_xboole_0(C_93) | ~m1_subset_1(B_94, k1_zfmisc_1(C_93)) | ~r2_hidden(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.66/1.39  tff(c_290, plain, (![A_95]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_95, '#skF_4'))), inference(resolution, [status(thm)], [c_59, c_288])).
% 2.66/1.39  tff(c_294, plain, (![A_96]: (~r2_hidden(A_96, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_290])).
% 2.66/1.39  tff(c_299, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_294])).
% 2.66/1.39  tff(c_44, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.66/1.39  tff(c_72, plain, (![A_71]: (v1_relat_1(k6_relat_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.66/1.39  tff(c_74, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_72])).
% 2.66/1.39  tff(c_42, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.66/1.39  tff(c_40, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.66/1.39  tff(c_260, plain, (![A_89]: (k10_relat_1(A_89, k2_relat_1(A_89))=k1_relat_1(A_89) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.66/1.39  tff(c_269, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_260])).
% 2.66/1.39  tff(c_273, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_74, c_42, c_269])).
% 2.66/1.39  tff(c_300, plain, (k10_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_299, c_299, c_299, c_273])).
% 2.66/1.39  tff(c_312, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_299, c_74])).
% 2.66/1.39  tff(c_8, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.39  tff(c_230, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k3_xboole_0(A_86, B_87))=k4_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.66/1.39  tff(c_114, plain, (![B_77, A_78]: (k5_xboole_0(B_77, A_78)=k5_xboole_0(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.66/1.39  tff(c_10, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.66/1.39  tff(c_130, plain, (![A_78]: (k5_xboole_0(k1_xboole_0, A_78)=A_78)), inference(superposition, [status(thm), theory('equality')], [c_114, c_10])).
% 2.66/1.39  tff(c_237, plain, (![B_87]: (k4_xboole_0(k1_xboole_0, B_87)=k3_xboole_0(k1_xboole_0, B_87))), inference(superposition, [status(thm), theory('equality')], [c_230, c_130])).
% 2.66/1.39  tff(c_246, plain, (![B_87]: (k3_xboole_0(k1_xboole_0, B_87)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_237])).
% 2.66/1.39  tff(c_301, plain, (![B_87]: (k3_xboole_0('#skF_4', B_87)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_299, c_299, c_246])).
% 2.66/1.39  tff(c_313, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_299, c_299, c_40])).
% 2.66/1.39  tff(c_427, plain, (![B_106, A_107]: (k10_relat_1(B_106, k3_xboole_0(k2_relat_1(B_106), A_107))=k10_relat_1(B_106, A_107) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.66/1.39  tff(c_436, plain, (![A_107]: (k10_relat_1('#skF_4', k3_xboole_0('#skF_4', A_107))=k10_relat_1('#skF_4', A_107) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_313, c_427])).
% 2.66/1.39  tff(c_440, plain, (![A_107]: (k10_relat_1('#skF_4', A_107)=k10_relat_1('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_301, c_436])).
% 2.66/1.39  tff(c_511, plain, (![A_107]: (k10_relat_1('#skF_4', A_107)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_300, c_440])).
% 2.66/1.39  tff(c_308, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_59])).
% 2.66/1.39  tff(c_307, plain, (![B_35]: (k2_zfmisc_1('#skF_4', B_35)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_299, c_299, c_28])).
% 2.66/1.39  tff(c_506, plain, (![A_115, B_116, C_117, D_118]: (k8_relset_1(A_115, B_116, C_117, D_118)=k10_relat_1(C_117, D_118) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.66/1.39  tff(c_555, plain, (![B_122, C_123, D_124]: (k8_relset_1('#skF_4', B_122, C_123, D_124)=k10_relat_1(C_123, D_124) | ~m1_subset_1(C_123, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_307, c_506])).
% 2.66/1.39  tff(c_557, plain, (![B_122, D_124]: (k8_relset_1('#skF_4', B_122, '#skF_4', D_124)=k10_relat_1('#skF_4', D_124))), inference(resolution, [status(thm)], [c_308, c_555])).
% 2.66/1.39  tff(c_559, plain, (![B_122, D_124]: (k8_relset_1('#skF_4', B_122, '#skF_4', D_124)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_511, c_557])).
% 2.66/1.39  tff(c_52, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.66/1.39  tff(c_309, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_299, c_299, c_52])).
% 2.66/1.39  tff(c_562, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_559, c_309])).
% 2.66/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.39  
% 2.66/1.39  Inference rules
% 2.66/1.39  ----------------------
% 2.66/1.39  #Ref     : 0
% 2.66/1.39  #Sup     : 118
% 2.66/1.39  #Fact    : 0
% 2.66/1.39  #Define  : 0
% 2.66/1.39  #Split   : 0
% 2.66/1.39  #Chain   : 0
% 2.66/1.39  #Close   : 0
% 2.66/1.39  
% 2.66/1.39  Ordering : KBO
% 2.66/1.39  
% 2.66/1.39  Simplification rules
% 2.66/1.39  ----------------------
% 2.66/1.39  #Subsume      : 1
% 2.66/1.39  #Demod        : 78
% 2.66/1.39  #Tautology    : 108
% 2.66/1.39  #SimpNegUnit  : 0
% 2.66/1.39  #BackRed      : 18
% 2.66/1.39  
% 2.66/1.39  #Partial instantiations: 0
% 2.66/1.39  #Strategies tried      : 1
% 2.66/1.39  
% 2.66/1.39  Timing (in seconds)
% 2.66/1.39  ----------------------
% 2.66/1.40  Preprocessing        : 0.36
% 2.66/1.40  Parsing              : 0.19
% 2.66/1.40  CNF conversion       : 0.03
% 2.66/1.40  Main loop            : 0.26
% 2.66/1.40  Inferencing          : 0.09
% 2.66/1.40  Reduction            : 0.09
% 2.66/1.40  Demodulation         : 0.07
% 2.66/1.40  BG Simplification    : 0.02
% 2.66/1.40  Subsumption          : 0.03
% 2.66/1.40  Abstraction          : 0.02
% 2.66/1.40  MUC search           : 0.00
% 2.66/1.40  Cooper               : 0.00
% 2.66/1.40  Total                : 0.66
% 2.66/1.40  Index Insertion      : 0.00
% 2.66/1.40  Index Deletion       : 0.00
% 2.66/1.40  Index Matching       : 0.00
% 2.66/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
