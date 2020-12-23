%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:30 EST 2020

% Result     : Theorem 4.71s
% Output     : CNFRefutation 5.09s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 152 expanded)
%              Number of leaves         :   32 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :  114 ( 266 expanded)
%              Number of equality atoms :    8 (  17 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(c_18,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_51,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_57,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_51])).

tff(c_61,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_57])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k7_relat_1(B_14,A_13),B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    ! [A_45,B_46] :
      ( v1_relat_1(A_45)
      | ~ v1_relat_1(B_46)
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_4,c_51])).

tff(c_69,plain,(
    ! [B_14,A_13] :
      ( v1_relat_1(k7_relat_1(B_14,A_13))
      | ~ v1_relat_1(B_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_62])).

tff(c_513,plain,(
    ! [C_144,A_145,B_146] :
      ( m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ r1_tarski(k2_relat_1(C_144),B_146)
      | ~ r1_tarski(k1_relat_1(C_144),A_145)
      | ~ v1_relat_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_348,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( k5_relset_1(A_106,B_107,C_108,D_109) = k7_relat_1(C_108,D_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_359,plain,(
    ! [D_109] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_109) = k7_relat_1('#skF_4',D_109) ),
    inference(resolution,[status(thm)],[c_38,c_348])).

tff(c_36,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_361,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_36])).

tff(c_552,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_513,c_361])).

tff(c_569,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_552])).

tff(c_572,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_69,c_569])).

tff(c_576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_572])).

tff(c_578,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_552])).

tff(c_117,plain,(
    ! [C_62,A_63,B_64] :
      ( v4_relat_1(C_62,A_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_126,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_117])).

tff(c_146,plain,(
    ! [C_71,A_72,B_73] :
      ( v4_relat_1(k7_relat_1(C_71,A_72),A_72)
      | ~ v4_relat_1(C_71,B_73)
      | ~ v1_relat_1(C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_150,plain,(
    ! [A_72] :
      ( v4_relat_1(k7_relat_1('#skF_4',A_72),A_72)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_126,c_146])).

tff(c_154,plain,(
    ! [A_72] : v4_relat_1(k7_relat_1('#skF_4',A_72),A_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_150])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_451,plain,(
    ! [A_129,B_130,C_131,D_132] :
      ( m1_subset_1(A_129,k1_zfmisc_1(k2_zfmisc_1(B_130,C_131)))
      | ~ r1_tarski(A_129,D_132)
      | ~ m1_subset_1(D_132,k1_zfmisc_1(k2_zfmisc_1(B_130,C_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_754,plain,(
    ! [B_189,A_190,B_191,C_192] :
      ( m1_subset_1(k7_relat_1(B_189,A_190),k1_zfmisc_1(k2_zfmisc_1(B_191,C_192)))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(k2_zfmisc_1(B_191,C_192)))
      | ~ v1_relat_1(B_189) ) ),
    inference(resolution,[status(thm)],[c_20,c_451])).

tff(c_28,plain,(
    ! [A_21,B_22,C_23] :
      ( k2_relset_1(A_21,B_22,C_23) = k2_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2144,plain,(
    ! [B_371,C_372,B_373,A_374] :
      ( k2_relset_1(B_371,C_372,k7_relat_1(B_373,A_374)) = k2_relat_1(k7_relat_1(B_373,A_374))
      | ~ m1_subset_1(B_373,k1_zfmisc_1(k2_zfmisc_1(B_371,C_372)))
      | ~ v1_relat_1(B_373) ) ),
    inference(resolution,[status(thm)],[c_754,c_28])).

tff(c_2158,plain,(
    ! [A_374] :
      ( k2_relset_1('#skF_1','#skF_3',k7_relat_1('#skF_4',A_374)) = k2_relat_1(k7_relat_1('#skF_4',A_374))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_2144])).

tff(c_2167,plain,(
    ! [A_375] : k2_relset_1('#skF_1','#skF_3',k7_relat_1('#skF_4',A_375)) = k2_relat_1(k7_relat_1('#skF_4',A_375)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_2158])).

tff(c_235,plain,(
    ! [A_92,B_93,C_94] :
      ( m1_subset_1(k2_relset_1(A_92,B_93,C_94),k1_zfmisc_1(B_93))
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_261,plain,(
    ! [A_92,B_93,C_94] :
      ( r1_tarski(k2_relset_1(A_92,B_93,C_94),B_93)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(resolution,[status(thm)],[c_235,c_2])).

tff(c_789,plain,(
    ! [B_191,C_192,B_189,A_190] :
      ( r1_tarski(k2_relset_1(B_191,C_192,k7_relat_1(B_189,A_190)),C_192)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(k2_zfmisc_1(B_191,C_192)))
      | ~ v1_relat_1(B_189) ) ),
    inference(resolution,[status(thm)],[c_754,c_261])).

tff(c_2176,plain,(
    ! [A_375] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_375)),'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2167,c_789])).

tff(c_2193,plain,(
    ! [A_375] : r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_375)),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_38,c_2176])).

tff(c_577,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_552])).

tff(c_579,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_577])).

tff(c_2221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2193,c_579])).

tff(c_2222,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_577])).

tff(c_2226,plain,
    ( ~ v4_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_2222])).

tff(c_2230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_154,c_2226])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.71/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.94  
% 4.71/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.94  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.71/1.94  
% 4.71/1.94  %Foreground sorts:
% 4.71/1.94  
% 4.71/1.94  
% 4.71/1.94  %Background operators:
% 4.71/1.94  
% 4.71/1.94  
% 4.71/1.94  %Foreground operators:
% 4.71/1.94  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.71/1.94  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 4.71/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.71/1.94  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.71/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.71/1.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.71/1.94  tff('#skF_2', type, '#skF_2': $i).
% 4.71/1.94  tff('#skF_3', type, '#skF_3': $i).
% 4.71/1.94  tff('#skF_1', type, '#skF_1': $i).
% 4.71/1.94  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.71/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.71/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.71/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.71/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.71/1.94  tff('#skF_4', type, '#skF_4': $i).
% 4.71/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.71/1.94  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.71/1.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.71/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.71/1.94  
% 5.09/1.95  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.09/1.95  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 5.09/1.95  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.09/1.95  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 5.09/1.95  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.09/1.95  tff(f_84, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 5.09/1.95  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 5.09/1.95  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.09/1.95  tff(f_52, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 5.09/1.95  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.09/1.95  tff(f_90, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_relset_1)).
% 5.09/1.95  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.09/1.95  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 5.09/1.95  tff(c_18, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.09/1.95  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.09/1.95  tff(c_51, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.09/1.95  tff(c_57, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_51])).
% 5.09/1.95  tff(c_61, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_57])).
% 5.09/1.95  tff(c_20, plain, (![B_14, A_13]: (r1_tarski(k7_relat_1(B_14, A_13), B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.09/1.95  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.09/1.95  tff(c_62, plain, (![A_45, B_46]: (v1_relat_1(A_45) | ~v1_relat_1(B_46) | ~r1_tarski(A_45, B_46))), inference(resolution, [status(thm)], [c_4, c_51])).
% 5.09/1.95  tff(c_69, plain, (![B_14, A_13]: (v1_relat_1(k7_relat_1(B_14, A_13)) | ~v1_relat_1(B_14))), inference(resolution, [status(thm)], [c_20, c_62])).
% 5.09/1.95  tff(c_513, plain, (![C_144, A_145, B_146]: (m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~r1_tarski(k2_relat_1(C_144), B_146) | ~r1_tarski(k1_relat_1(C_144), A_145) | ~v1_relat_1(C_144))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.09/1.95  tff(c_348, plain, (![A_106, B_107, C_108, D_109]: (k5_relset_1(A_106, B_107, C_108, D_109)=k7_relat_1(C_108, D_109) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.09/1.95  tff(c_359, plain, (![D_109]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_109)=k7_relat_1('#skF_4', D_109))), inference(resolution, [status(thm)], [c_38, c_348])).
% 5.09/1.95  tff(c_36, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.09/1.95  tff(c_361, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_359, c_36])).
% 5.09/1.95  tff(c_552, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_513, c_361])).
% 5.09/1.95  tff(c_569, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_552])).
% 5.09/1.95  tff(c_572, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_69, c_569])).
% 5.09/1.95  tff(c_576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_572])).
% 5.09/1.95  tff(c_578, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_552])).
% 5.09/1.95  tff(c_117, plain, (![C_62, A_63, B_64]: (v4_relat_1(C_62, A_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.09/1.95  tff(c_126, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_117])).
% 5.09/1.95  tff(c_146, plain, (![C_71, A_72, B_73]: (v4_relat_1(k7_relat_1(C_71, A_72), A_72) | ~v4_relat_1(C_71, B_73) | ~v1_relat_1(C_71))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.09/1.95  tff(c_150, plain, (![A_72]: (v4_relat_1(k7_relat_1('#skF_4', A_72), A_72) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_126, c_146])).
% 5.09/1.95  tff(c_154, plain, (![A_72]: (v4_relat_1(k7_relat_1('#skF_4', A_72), A_72))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_150])).
% 5.09/1.95  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.09/1.95  tff(c_451, plain, (![A_129, B_130, C_131, D_132]: (m1_subset_1(A_129, k1_zfmisc_1(k2_zfmisc_1(B_130, C_131))) | ~r1_tarski(A_129, D_132) | ~m1_subset_1(D_132, k1_zfmisc_1(k2_zfmisc_1(B_130, C_131))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.09/1.95  tff(c_754, plain, (![B_189, A_190, B_191, C_192]: (m1_subset_1(k7_relat_1(B_189, A_190), k1_zfmisc_1(k2_zfmisc_1(B_191, C_192))) | ~m1_subset_1(B_189, k1_zfmisc_1(k2_zfmisc_1(B_191, C_192))) | ~v1_relat_1(B_189))), inference(resolution, [status(thm)], [c_20, c_451])).
% 5.09/1.95  tff(c_28, plain, (![A_21, B_22, C_23]: (k2_relset_1(A_21, B_22, C_23)=k2_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.09/1.95  tff(c_2144, plain, (![B_371, C_372, B_373, A_374]: (k2_relset_1(B_371, C_372, k7_relat_1(B_373, A_374))=k2_relat_1(k7_relat_1(B_373, A_374)) | ~m1_subset_1(B_373, k1_zfmisc_1(k2_zfmisc_1(B_371, C_372))) | ~v1_relat_1(B_373))), inference(resolution, [status(thm)], [c_754, c_28])).
% 5.09/1.95  tff(c_2158, plain, (![A_374]: (k2_relset_1('#skF_1', '#skF_3', k7_relat_1('#skF_4', A_374))=k2_relat_1(k7_relat_1('#skF_4', A_374)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_2144])).
% 5.09/1.95  tff(c_2167, plain, (![A_375]: (k2_relset_1('#skF_1', '#skF_3', k7_relat_1('#skF_4', A_375))=k2_relat_1(k7_relat_1('#skF_4', A_375)))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_2158])).
% 5.09/1.95  tff(c_235, plain, (![A_92, B_93, C_94]: (m1_subset_1(k2_relset_1(A_92, B_93, C_94), k1_zfmisc_1(B_93)) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.09/1.95  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.09/1.95  tff(c_261, plain, (![A_92, B_93, C_94]: (r1_tarski(k2_relset_1(A_92, B_93, C_94), B_93) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(resolution, [status(thm)], [c_235, c_2])).
% 5.09/1.95  tff(c_789, plain, (![B_191, C_192, B_189, A_190]: (r1_tarski(k2_relset_1(B_191, C_192, k7_relat_1(B_189, A_190)), C_192) | ~m1_subset_1(B_189, k1_zfmisc_1(k2_zfmisc_1(B_191, C_192))) | ~v1_relat_1(B_189))), inference(resolution, [status(thm)], [c_754, c_261])).
% 5.09/1.95  tff(c_2176, plain, (![A_375]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_375)), '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2167, c_789])).
% 5.09/1.95  tff(c_2193, plain, (![A_375]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_375)), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_38, c_2176])).
% 5.09/1.95  tff(c_577, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_552])).
% 5.09/1.95  tff(c_579, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_577])).
% 5.09/1.95  tff(c_2221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2193, c_579])).
% 5.09/1.95  tff(c_2222, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_577])).
% 5.09/1.95  tff(c_2226, plain, (~v4_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_2222])).
% 5.09/1.95  tff(c_2230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_578, c_154, c_2226])).
% 5.09/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.09/1.95  
% 5.09/1.95  Inference rules
% 5.09/1.95  ----------------------
% 5.09/1.95  #Ref     : 0
% 5.09/1.95  #Sup     : 514
% 5.09/1.95  #Fact    : 0
% 5.09/1.95  #Define  : 0
% 5.09/1.95  #Split   : 8
% 5.09/1.95  #Chain   : 0
% 5.09/1.95  #Close   : 0
% 5.09/1.95  
% 5.09/1.95  Ordering : KBO
% 5.09/1.95  
% 5.09/1.95  Simplification rules
% 5.09/1.95  ----------------------
% 5.09/1.95  #Subsume      : 98
% 5.09/1.95  #Demod        : 102
% 5.09/1.95  #Tautology    : 45
% 5.09/1.95  #SimpNegUnit  : 0
% 5.09/1.95  #BackRed      : 4
% 5.09/1.95  
% 5.09/1.95  #Partial instantiations: 0
% 5.09/1.95  #Strategies tried      : 1
% 5.09/1.95  
% 5.09/1.95  Timing (in seconds)
% 5.09/1.95  ----------------------
% 5.09/1.96  Preprocessing        : 0.33
% 5.09/1.96  Parsing              : 0.18
% 5.09/1.96  CNF conversion       : 0.02
% 5.09/1.96  Main loop            : 0.83
% 5.09/1.96  Inferencing          : 0.29
% 5.09/1.96  Reduction            : 0.24
% 5.09/1.96  Demodulation         : 0.16
% 5.09/1.96  BG Simplification    : 0.04
% 5.09/1.96  Subsumption          : 0.20
% 5.09/1.96  Abstraction          : 0.04
% 5.09/1.96  MUC search           : 0.00
% 5.09/1.96  Cooper               : 0.00
% 5.09/1.96  Total                : 1.20
% 5.09/1.96  Index Insertion      : 0.00
% 5.09/1.96  Index Deletion       : 0.00
% 5.09/1.96  Index Matching       : 0.00
% 5.09/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
