%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:05 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 271 expanded)
%              Number of leaves         :   45 ( 114 expanded)
%              Depth                    :   11
%              Number of atoms          :   83 ( 496 expanded)
%              Number of equality atoms :   44 ( 158 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_96,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_71,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_59,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_70,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_28,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_30,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_50,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_46,plain,(
    ! [A_46] :
      ( r2_hidden('#skF_1'(A_46),A_46)
      | k1_xboole_0 = A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_24,plain,(
    ! [B_32] : k2_zfmisc_1(k1_xboole_0,B_32) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_55,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_50])).

tff(c_303,plain,(
    ! [C_90,B_91,A_92] :
      ( ~ v1_xboole_0(C_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(C_90))
      | ~ r2_hidden(A_92,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_305,plain,(
    ! [A_92] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_92,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_55,c_303])).

tff(c_309,plain,(
    ! [A_93] : ~ r2_hidden(A_93,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_305])).

tff(c_314,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_309])).

tff(c_40,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_68,plain,(
    ! [A_68] : v1_relat_1(k6_relat_1(A_68)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_70,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_68])).

tff(c_38,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_275,plain,(
    ! [A_86] :
      ( k10_relat_1(A_86,k2_relat_1(A_86)) = k1_relat_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_284,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_275])).

tff(c_288,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_38,c_284])).

tff(c_315,plain,(
    k10_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_314,c_314,c_288])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_383,plain,(
    ! [A_97] : k3_xboole_0(A_97,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_314,c_4])).

tff(c_6,plain,(
    ! [B_3,A_2] : k2_tarski(B_3,A_2) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_143,plain,(
    ! [A_77,B_78] : k1_setfam_1(k2_tarski(A_77,B_78)) = k3_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_158,plain,(
    ! [B_79,A_80] : k1_setfam_1(k2_tarski(B_79,A_80)) = k3_xboole_0(A_80,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_143])).

tff(c_26,plain,(
    ! [A_33,B_34] : k1_setfam_1(k2_tarski(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_164,plain,(
    ! [B_79,A_80] : k3_xboole_0(B_79,A_80) = k3_xboole_0(A_80,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_26])).

tff(c_392,plain,(
    ! [A_97] : k3_xboole_0('#skF_4',A_97) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_164])).

tff(c_325,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_70])).

tff(c_326,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_314,c_36])).

tff(c_343,plain,(
    ! [B_94,A_95] :
      ( k10_relat_1(B_94,k3_xboole_0(k2_relat_1(B_94),A_95)) = k10_relat_1(B_94,A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_352,plain,(
    ! [A_95] :
      ( k10_relat_1('#skF_4',k3_xboole_0('#skF_4',A_95)) = k10_relat_1('#skF_4',A_95)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_343])).

tff(c_364,plain,(
    ! [A_95] : k10_relat_1('#skF_4',k3_xboole_0('#skF_4',A_95)) = k10_relat_1('#skF_4',A_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_352])).

tff(c_498,plain,(
    ! [A_95] : k10_relat_1('#skF_4',A_95) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_392,c_364])).

tff(c_321,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_55])).

tff(c_324,plain,(
    ! [B_32] : k2_zfmisc_1('#skF_4',B_32) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_314,c_24])).

tff(c_589,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( k8_relset_1(A_115,B_116,C_117,D_118) = k10_relat_1(C_117,D_118)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_615,plain,(
    ! [B_130,C_131,D_132] :
      ( k8_relset_1('#skF_4',B_130,C_131,D_132) = k10_relat_1(C_131,D_132)
      | ~ m1_subset_1(C_131,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_589])).

tff(c_617,plain,(
    ! [B_130,D_132] : k8_relset_1('#skF_4',B_130,'#skF_4',D_132) = k10_relat_1('#skF_4',D_132) ),
    inference(resolution,[status(thm)],[c_321,c_615])).

tff(c_619,plain,(
    ! [B_130,D_132] : k8_relset_1('#skF_4',B_130,'#skF_4',D_132) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_617])).

tff(c_48,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_319,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_314,c_48])).

tff(c_622,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:39:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.40  
% 2.69/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.41  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.69/1.41  
% 2.69/1.41  %Foreground sorts:
% 2.69/1.41  
% 2.69/1.41  
% 2.69/1.41  %Background operators:
% 2.69/1.41  
% 2.69/1.41  
% 2.69/1.41  %Foreground operators:
% 2.69/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.41  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.69/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.69/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.69/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.69/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.69/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.69/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.69/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.69/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.69/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.41  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.69/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.69/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.69/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.69/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.69/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.69/1.41  
% 2.69/1.42  tff(f_96, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.69/1.42  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.69/1.42  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.69/1.42  tff(f_105, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 2.69/1.42  tff(f_57, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.69/1.42  tff(f_71, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.69/1.42  tff(f_59, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.69/1.42  tff(f_70, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.69/1.42  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.69/1.42  tff(f_28, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.69/1.42  tff(f_30, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.69/1.42  tff(f_50, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.69/1.42  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 2.69/1.42  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.69/1.42  tff(c_46, plain, (![A_46]: (r2_hidden('#skF_1'(A_46), A_46) | k1_xboole_0=A_46)), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.69/1.42  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.69/1.42  tff(c_24, plain, (![B_32]: (k2_zfmisc_1(k1_xboole_0, B_32)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.69/1.42  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.69/1.42  tff(c_55, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_50])).
% 2.69/1.42  tff(c_303, plain, (![C_90, B_91, A_92]: (~v1_xboole_0(C_90) | ~m1_subset_1(B_91, k1_zfmisc_1(C_90)) | ~r2_hidden(A_92, B_91))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.69/1.42  tff(c_305, plain, (![A_92]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_92, '#skF_4'))), inference(resolution, [status(thm)], [c_55, c_303])).
% 2.69/1.42  tff(c_309, plain, (![A_93]: (~r2_hidden(A_93, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_305])).
% 2.69/1.42  tff(c_314, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_46, c_309])).
% 2.69/1.42  tff(c_40, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.69/1.42  tff(c_68, plain, (![A_68]: (v1_relat_1(k6_relat_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.69/1.42  tff(c_70, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_68])).
% 2.69/1.42  tff(c_38, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.69/1.42  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.69/1.42  tff(c_275, plain, (![A_86]: (k10_relat_1(A_86, k2_relat_1(A_86))=k1_relat_1(A_86) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.69/1.42  tff(c_284, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_275])).
% 2.69/1.42  tff(c_288, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_38, c_284])).
% 2.69/1.42  tff(c_315, plain, (k10_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_314, c_314, c_314, c_288])).
% 2.69/1.42  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.69/1.42  tff(c_383, plain, (![A_97]: (k3_xboole_0(A_97, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_314, c_314, c_4])).
% 2.69/1.42  tff(c_6, plain, (![B_3, A_2]: (k2_tarski(B_3, A_2)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.69/1.42  tff(c_143, plain, (![A_77, B_78]: (k1_setfam_1(k2_tarski(A_77, B_78))=k3_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.69/1.42  tff(c_158, plain, (![B_79, A_80]: (k1_setfam_1(k2_tarski(B_79, A_80))=k3_xboole_0(A_80, B_79))), inference(superposition, [status(thm), theory('equality')], [c_6, c_143])).
% 2.69/1.42  tff(c_26, plain, (![A_33, B_34]: (k1_setfam_1(k2_tarski(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.69/1.42  tff(c_164, plain, (![B_79, A_80]: (k3_xboole_0(B_79, A_80)=k3_xboole_0(A_80, B_79))), inference(superposition, [status(thm), theory('equality')], [c_158, c_26])).
% 2.69/1.42  tff(c_392, plain, (![A_97]: (k3_xboole_0('#skF_4', A_97)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_383, c_164])).
% 2.69/1.42  tff(c_325, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_314, c_70])).
% 2.69/1.42  tff(c_326, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_314, c_314, c_36])).
% 2.69/1.42  tff(c_343, plain, (![B_94, A_95]: (k10_relat_1(B_94, k3_xboole_0(k2_relat_1(B_94), A_95))=k10_relat_1(B_94, A_95) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.69/1.42  tff(c_352, plain, (![A_95]: (k10_relat_1('#skF_4', k3_xboole_0('#skF_4', A_95))=k10_relat_1('#skF_4', A_95) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_326, c_343])).
% 2.69/1.42  tff(c_364, plain, (![A_95]: (k10_relat_1('#skF_4', k3_xboole_0('#skF_4', A_95))=k10_relat_1('#skF_4', A_95))), inference(demodulation, [status(thm), theory('equality')], [c_325, c_352])).
% 2.69/1.42  tff(c_498, plain, (![A_95]: (k10_relat_1('#skF_4', A_95)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_315, c_392, c_364])).
% 2.69/1.42  tff(c_321, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_55])).
% 2.69/1.42  tff(c_324, plain, (![B_32]: (k2_zfmisc_1('#skF_4', B_32)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_314, c_314, c_24])).
% 2.69/1.42  tff(c_589, plain, (![A_115, B_116, C_117, D_118]: (k8_relset_1(A_115, B_116, C_117, D_118)=k10_relat_1(C_117, D_118) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.69/1.42  tff(c_615, plain, (![B_130, C_131, D_132]: (k8_relset_1('#skF_4', B_130, C_131, D_132)=k10_relat_1(C_131, D_132) | ~m1_subset_1(C_131, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_324, c_589])).
% 2.69/1.42  tff(c_617, plain, (![B_130, D_132]: (k8_relset_1('#skF_4', B_130, '#skF_4', D_132)=k10_relat_1('#skF_4', D_132))), inference(resolution, [status(thm)], [c_321, c_615])).
% 2.69/1.42  tff(c_619, plain, (![B_130, D_132]: (k8_relset_1('#skF_4', B_130, '#skF_4', D_132)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_498, c_617])).
% 2.69/1.42  tff(c_48, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.69/1.42  tff(c_319, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_314, c_314, c_48])).
% 2.69/1.42  tff(c_622, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_619, c_319])).
% 2.69/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.42  
% 2.69/1.42  Inference rules
% 2.69/1.42  ----------------------
% 2.69/1.42  #Ref     : 0
% 2.69/1.42  #Sup     : 136
% 2.69/1.42  #Fact    : 0
% 2.69/1.42  #Define  : 0
% 2.69/1.42  #Split   : 0
% 2.69/1.42  #Chain   : 0
% 2.69/1.42  #Close   : 0
% 2.69/1.42  
% 2.69/1.42  Ordering : KBO
% 2.69/1.42  
% 2.69/1.42  Simplification rules
% 2.69/1.42  ----------------------
% 2.69/1.42  #Subsume      : 5
% 2.69/1.42  #Demod        : 77
% 2.69/1.42  #Tautology    : 119
% 2.69/1.42  #SimpNegUnit  : 0
% 2.69/1.42  #BackRed      : 16
% 2.69/1.42  
% 2.69/1.42  #Partial instantiations: 0
% 2.69/1.42  #Strategies tried      : 1
% 2.69/1.42  
% 2.69/1.42  Timing (in seconds)
% 2.69/1.42  ----------------------
% 2.69/1.42  Preprocessing        : 0.35
% 2.69/1.42  Parsing              : 0.20
% 2.69/1.42  CNF conversion       : 0.02
% 2.69/1.42  Main loop            : 0.26
% 2.69/1.42  Inferencing          : 0.10
% 2.69/1.42  Reduction            : 0.09
% 2.69/1.43  Demodulation         : 0.07
% 2.69/1.43  BG Simplification    : 0.02
% 2.69/1.43  Subsumption          : 0.04
% 2.69/1.43  Abstraction          : 0.02
% 2.69/1.43  MUC search           : 0.00
% 2.69/1.43  Cooper               : 0.00
% 2.69/1.43  Total                : 0.65
% 2.69/1.43  Index Insertion      : 0.00
% 2.69/1.43  Index Deletion       : 0.00
% 2.69/1.43  Index Matching       : 0.00
% 2.69/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
