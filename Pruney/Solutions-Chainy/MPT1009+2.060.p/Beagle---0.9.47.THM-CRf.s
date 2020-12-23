%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:50 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 187 expanded)
%              Number of leaves         :   38 (  79 expanded)
%              Depth                    :    9
%              Number of atoms          :  117 ( 379 expanded)
%              Number of equality atoms :   51 ( 125 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_112,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_125,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_112])).

tff(c_26,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k9_relat_1(B_14,A_13),k2_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    ! [A_16] :
      ( k1_relat_1(A_16) != k1_xboole_0
      | k1_xboole_0 = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_134,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_125,c_32])).

tff(c_152,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_271,plain,(
    ! [B_87,A_88] :
      ( k1_tarski(k1_funct_1(B_87,A_88)) = k2_relat_1(B_87)
      | k1_tarski(A_88) != k1_relat_1(B_87)
      | ~ v1_funct_1(B_87)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_44,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_277,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_44])).

tff(c_295,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_52,c_277])).

tff(c_299,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_295])).

tff(c_171,plain,(
    ! [C_59,A_60,B_61] :
      ( v4_relat_1(C_59,A_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_184,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_171])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_421,plain,(
    ! [B_104,C_105,A_106] :
      ( k2_tarski(B_104,C_105) = A_106
      | k1_tarski(C_105) = A_106
      | k1_tarski(B_104) = A_106
      | k1_xboole_0 = A_106
      | ~ r1_tarski(A_106,k2_tarski(B_104,C_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_441,plain,(
    ! [A_1,A_106] :
      ( k2_tarski(A_1,A_1) = A_106
      | k1_tarski(A_1) = A_106
      | k1_tarski(A_1) = A_106
      | k1_xboole_0 = A_106
      | ~ r1_tarski(A_106,k1_tarski(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_421])).

tff(c_603,plain,(
    ! [A_124,A_125] :
      ( k1_tarski(A_124) = A_125
      | k1_tarski(A_124) = A_125
      | k1_tarski(A_124) = A_125
      | k1_xboole_0 = A_125
      | ~ r1_tarski(A_125,k1_tarski(A_124)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_441])).

tff(c_652,plain,(
    ! [A_128,B_129] :
      ( k1_tarski(A_128) = k1_relat_1(B_129)
      | k1_relat_1(B_129) = k1_xboole_0
      | ~ v4_relat_1(B_129,k1_tarski(A_128))
      | ~ v1_relat_1(B_129) ) ),
    inference(resolution,[status(thm)],[c_24,c_603])).

tff(c_690,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_184,c_652])).

tff(c_724,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_690])).

tff(c_726,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_299,c_724])).

tff(c_728,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_295])).

tff(c_733,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_728,c_48])).

tff(c_42,plain,(
    ! [A_25,B_26,C_27,D_28] :
      ( k7_relset_1(A_25,B_26,C_27,D_28) = k9_relat_1(C_27,D_28)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_808,plain,(
    ! [D_28] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_28) = k9_relat_1('#skF_4',D_28) ),
    inference(resolution,[status(thm)],[c_733,c_42])).

tff(c_727,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_295])).

tff(c_898,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_728,c_727])).

tff(c_899,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_898])).

tff(c_911,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_899])).

tff(c_915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_911])).

tff(c_916,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_85,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_97,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_85])).

tff(c_922,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_916,c_97])).

tff(c_28,plain,(
    ! [A_15] : k9_relat_1(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_923,plain,(
    ! [A_15] : k9_relat_1('#skF_4',A_15) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_916,c_916,c_28])).

tff(c_924,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_916,c_14])).

tff(c_1061,plain,(
    ! [A_177,B_178,C_179,D_180] :
      ( k7_relset_1(A_177,B_178,C_179,D_180) = k9_relat_1(C_179,D_180)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1064,plain,(
    ! [A_177,B_178,D_180] : k7_relset_1(A_177,B_178,'#skF_4',D_180) = k9_relat_1('#skF_4',D_180) ),
    inference(resolution,[status(thm)],[c_924,c_1061])).

tff(c_1069,plain,(
    ! [A_177,B_178,D_180] : k7_relset_1(A_177,B_178,'#skF_4',D_180) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_923,c_1064])).

tff(c_1071,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1069,c_44])).

tff(c_1074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_922,c_1071])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.62  
% 2.99/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.62  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.29/1.62  
% 3.29/1.62  %Foreground sorts:
% 3.29/1.62  
% 3.29/1.62  
% 3.29/1.62  %Background operators:
% 3.29/1.62  
% 3.29/1.62  
% 3.29/1.62  %Foreground operators:
% 3.29/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.29/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.29/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.29/1.62  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.29/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.29/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.29/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.29/1.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.29/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.29/1.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.29/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.29/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.29/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.29/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.29/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.29/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.29/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.29/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.29/1.62  
% 3.29/1.64  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.29/1.64  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.29/1.64  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.29/1.64  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.29/1.64  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.29/1.64  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.29/1.64  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.29/1.64  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.29/1.64  tff(f_42, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.29/1.64  tff(f_96, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.29/1.64  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.29/1.64  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.29/1.64  tff(f_66, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 3.29/1.64  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.29/1.64  tff(c_112, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.29/1.64  tff(c_125, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_112])).
% 3.29/1.64  tff(c_26, plain, (![B_14, A_13]: (r1_tarski(k9_relat_1(B_14, A_13), k2_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.29/1.64  tff(c_32, plain, (![A_16]: (k1_relat_1(A_16)!=k1_xboole_0 | k1_xboole_0=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.29/1.64  tff(c_134, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_125, c_32])).
% 3.29/1.64  tff(c_152, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_134])).
% 3.29/1.64  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.29/1.64  tff(c_271, plain, (![B_87, A_88]: (k1_tarski(k1_funct_1(B_87, A_88))=k2_relat_1(B_87) | k1_tarski(A_88)!=k1_relat_1(B_87) | ~v1_funct_1(B_87) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.29/1.64  tff(c_44, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.29/1.64  tff(c_277, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_271, c_44])).
% 3.29/1.64  tff(c_295, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_52, c_277])).
% 3.29/1.64  tff(c_299, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_295])).
% 3.29/1.64  tff(c_171, plain, (![C_59, A_60, B_61]: (v4_relat_1(C_59, A_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.29/1.64  tff(c_184, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_171])).
% 3.29/1.64  tff(c_24, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.29/1.64  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.29/1.64  tff(c_421, plain, (![B_104, C_105, A_106]: (k2_tarski(B_104, C_105)=A_106 | k1_tarski(C_105)=A_106 | k1_tarski(B_104)=A_106 | k1_xboole_0=A_106 | ~r1_tarski(A_106, k2_tarski(B_104, C_105)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.29/1.64  tff(c_441, plain, (![A_1, A_106]: (k2_tarski(A_1, A_1)=A_106 | k1_tarski(A_1)=A_106 | k1_tarski(A_1)=A_106 | k1_xboole_0=A_106 | ~r1_tarski(A_106, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_421])).
% 3.29/1.64  tff(c_603, plain, (![A_124, A_125]: (k1_tarski(A_124)=A_125 | k1_tarski(A_124)=A_125 | k1_tarski(A_124)=A_125 | k1_xboole_0=A_125 | ~r1_tarski(A_125, k1_tarski(A_124)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_441])).
% 3.29/1.64  tff(c_652, plain, (![A_128, B_129]: (k1_tarski(A_128)=k1_relat_1(B_129) | k1_relat_1(B_129)=k1_xboole_0 | ~v4_relat_1(B_129, k1_tarski(A_128)) | ~v1_relat_1(B_129))), inference(resolution, [status(thm)], [c_24, c_603])).
% 3.29/1.64  tff(c_690, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_184, c_652])).
% 3.29/1.64  tff(c_724, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_125, c_690])).
% 3.29/1.64  tff(c_726, plain, $false, inference(negUnitSimplification, [status(thm)], [c_152, c_299, c_724])).
% 3.29/1.64  tff(c_728, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_295])).
% 3.29/1.64  tff(c_733, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_728, c_48])).
% 3.29/1.64  tff(c_42, plain, (![A_25, B_26, C_27, D_28]: (k7_relset_1(A_25, B_26, C_27, D_28)=k9_relat_1(C_27, D_28) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.29/1.64  tff(c_808, plain, (![D_28]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_28)=k9_relat_1('#skF_4', D_28))), inference(resolution, [status(thm)], [c_733, c_42])).
% 3.29/1.64  tff(c_727, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_295])).
% 3.29/1.64  tff(c_898, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_728, c_727])).
% 3.29/1.64  tff(c_899, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_808, c_898])).
% 3.29/1.64  tff(c_911, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_899])).
% 3.29/1.64  tff(c_915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_911])).
% 3.29/1.64  tff(c_916, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_134])).
% 3.29/1.64  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.29/1.64  tff(c_85, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.29/1.64  tff(c_97, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_85])).
% 3.29/1.64  tff(c_922, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_916, c_97])).
% 3.29/1.64  tff(c_28, plain, (![A_15]: (k9_relat_1(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.29/1.64  tff(c_923, plain, (![A_15]: (k9_relat_1('#skF_4', A_15)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_916, c_916, c_28])).
% 3.29/1.64  tff(c_924, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_916, c_14])).
% 3.29/1.64  tff(c_1061, plain, (![A_177, B_178, C_179, D_180]: (k7_relset_1(A_177, B_178, C_179, D_180)=k9_relat_1(C_179, D_180) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.29/1.64  tff(c_1064, plain, (![A_177, B_178, D_180]: (k7_relset_1(A_177, B_178, '#skF_4', D_180)=k9_relat_1('#skF_4', D_180))), inference(resolution, [status(thm)], [c_924, c_1061])).
% 3.29/1.64  tff(c_1069, plain, (![A_177, B_178, D_180]: (k7_relset_1(A_177, B_178, '#skF_4', D_180)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_923, c_1064])).
% 3.29/1.64  tff(c_1071, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1069, c_44])).
% 3.29/1.64  tff(c_1074, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_922, c_1071])).
% 3.29/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.64  
% 3.29/1.64  Inference rules
% 3.29/1.64  ----------------------
% 3.29/1.64  #Ref     : 0
% 3.29/1.64  #Sup     : 188
% 3.29/1.64  #Fact    : 0
% 3.29/1.64  #Define  : 0
% 3.29/1.64  #Split   : 5
% 3.29/1.64  #Chain   : 0
% 3.29/1.64  #Close   : 0
% 3.29/1.64  
% 3.29/1.64  Ordering : KBO
% 3.29/1.64  
% 3.29/1.64  Simplification rules
% 3.29/1.64  ----------------------
% 3.29/1.64  #Subsume      : 2
% 3.29/1.64  #Demod        : 127
% 3.29/1.64  #Tautology    : 78
% 3.29/1.64  #SimpNegUnit  : 10
% 3.29/1.64  #BackRed      : 17
% 3.29/1.64  
% 3.29/1.64  #Partial instantiations: 0
% 3.29/1.64  #Strategies tried      : 1
% 3.29/1.64  
% 3.29/1.64  Timing (in seconds)
% 3.29/1.64  ----------------------
% 3.29/1.64  Preprocessing        : 0.43
% 3.29/1.64  Parsing              : 0.23
% 3.29/1.64  CNF conversion       : 0.03
% 3.29/1.64  Main loop            : 0.40
% 3.29/1.64  Inferencing          : 0.15
% 3.29/1.64  Reduction            : 0.14
% 3.29/1.64  Demodulation         : 0.10
% 3.29/1.64  BG Simplification    : 0.02
% 3.29/1.64  Subsumption          : 0.06
% 3.29/1.64  Abstraction          : 0.02
% 3.29/1.64  MUC search           : 0.00
% 3.29/1.64  Cooper               : 0.00
% 3.29/1.64  Total                : 0.86
% 3.29/1.64  Index Insertion      : 0.00
% 3.29/1.64  Index Deletion       : 0.00
% 3.29/1.64  Index Matching       : 0.00
% 3.29/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
