%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:05 EST 2020

% Result     : Theorem 8.87s
% Output     : CNFRefutation 8.87s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 114 expanded)
%              Number of leaves         :   37 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  110 ( 187 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_44,plain,(
    ! [A_33,B_34] : v1_relat_1(k2_zfmisc_1(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_95,plain,(
    ! [B_59,A_60] :
      ( v1_relat_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_101,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_95])).

tff(c_105,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_101])).

tff(c_176,plain,(
    ! [C_76,B_77,A_78] :
      ( v5_relat_1(C_76,B_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_185,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_176])).

tff(c_40,plain,(
    ! [B_31,A_30] :
      ( r1_tarski(k2_relat_1(B_31),A_30)
      | ~ v5_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_131,plain,(
    ! [C_67,A_68,B_69] :
      ( v4_relat_1(C_67,A_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_140,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_131])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(A_4,k2_xboole_0(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k1_relat_1(B_29),A_28)
      | ~ v4_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(k1_zfmisc_1(A_18),k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [C_15,A_11] :
      ( r2_hidden(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_252,plain,(
    ! [A_93,C_94,B_95] :
      ( m1_subset_1(A_93,C_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(C_94))
      | ~ r2_hidden(A_93,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_260,plain,(
    ! [A_97,B_98,A_99] :
      ( m1_subset_1(A_97,B_98)
      | ~ r2_hidden(A_97,A_99)
      | ~ r1_tarski(A_99,B_98) ) ),
    inference(resolution,[status(thm)],[c_28,c_252])).

tff(c_344,plain,(
    ! [C_118,B_119,A_120] :
      ( m1_subset_1(C_118,B_119)
      | ~ r1_tarski(k1_zfmisc_1(A_120),B_119)
      | ~ r1_tarski(C_118,A_120) ) ),
    inference(resolution,[status(thm)],[c_12,c_260])).

tff(c_361,plain,(
    ! [C_124,B_125,A_126] :
      ( m1_subset_1(C_124,k1_zfmisc_1(B_125))
      | ~ r1_tarski(C_124,A_126)
      | ~ r1_tarski(A_126,B_125) ) ),
    inference(resolution,[status(thm)],[c_24,c_344])).

tff(c_6455,plain,(
    ! [B_808,B_809,A_810] :
      ( m1_subset_1(k1_relat_1(B_808),k1_zfmisc_1(B_809))
      | ~ r1_tarski(A_810,B_809)
      | ~ v4_relat_1(B_808,A_810)
      | ~ v1_relat_1(B_808) ) ),
    inference(resolution,[status(thm)],[c_36,c_361])).

tff(c_6637,plain,(
    ! [B_813,A_814,B_815] :
      ( m1_subset_1(k1_relat_1(B_813),k1_zfmisc_1(k2_xboole_0(A_814,B_815)))
      | ~ v4_relat_1(B_813,A_814)
      | ~ v1_relat_1(B_813) ) ),
    inference(resolution,[status(thm)],[c_4,c_6455])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6652,plain,(
    ! [B_816,A_817,B_818] :
      ( r1_tarski(k1_relat_1(B_816),k2_xboole_0(A_817,B_818))
      | ~ v4_relat_1(B_816,A_817)
      | ~ v1_relat_1(B_816) ) ),
    inference(resolution,[status(thm)],[c_6637,c_26])).

tff(c_42,plain,(
    ! [A_32] :
      ( k2_xboole_0(k1_relat_1(A_32),k2_relat_1(A_32)) = k3_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_267,plain,(
    ! [A_103,C_104,B_105] :
      ( r1_tarski(k2_xboole_0(A_103,C_104),B_105)
      | ~ r1_tarski(C_104,B_105)
      | ~ r1_tarski(A_103,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_803,plain,(
    ! [A_216,B_217] :
      ( r1_tarski(k3_relat_1(A_216),B_217)
      | ~ r1_tarski(k2_relat_1(A_216),B_217)
      | ~ r1_tarski(k1_relat_1(A_216),B_217)
      | ~ v1_relat_1(A_216) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_267])).

tff(c_50,plain,(
    ~ r1_tarski(k3_relat_1('#skF_5'),k2_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_829,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),k2_xboole_0('#skF_3','#skF_4'))
    | ~ r1_tarski(k1_relat_1('#skF_5'),k2_xboole_0('#skF_3','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_803,c_50])).

tff(c_841,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),k2_xboole_0('#skF_3','#skF_4'))
    | ~ r1_tarski(k1_relat_1('#skF_5'),k2_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_829])).

tff(c_849,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),k2_xboole_0('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_841])).

tff(c_6674,plain,
    ( ~ v4_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6652,c_849])).

tff(c_6698,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_140,c_6674])).

tff(c_6699,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),k2_xboole_0('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_841])).

tff(c_6710,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_6699])).

tff(c_6713,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_6710])).

tff(c_6717,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_185,c_6713])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:58:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.87/2.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.87/2.91  
% 8.87/2.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.87/2.91  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 8.87/2.91  
% 8.87/2.91  %Foreground sorts:
% 8.87/2.91  
% 8.87/2.91  
% 8.87/2.91  %Background operators:
% 8.87/2.91  
% 8.87/2.91  
% 8.87/2.91  %Foreground operators:
% 8.87/2.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.87/2.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.87/2.91  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 8.87/2.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.87/2.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.87/2.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.87/2.91  tff('#skF_5', type, '#skF_5': $i).
% 8.87/2.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.87/2.91  tff('#skF_3', type, '#skF_3': $i).
% 8.87/2.91  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.87/2.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.87/2.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.87/2.91  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.87/2.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.87/2.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.87/2.92  tff('#skF_4', type, '#skF_4': $i).
% 8.87/2.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.87/2.92  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.87/2.92  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.87/2.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.87/2.92  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.87/2.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.87/2.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.87/2.92  
% 8.87/2.93  tff(f_87, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.87/2.93  tff(f_98, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 8.87/2.93  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.87/2.93  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.87/2.93  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 8.87/2.93  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 8.87/2.93  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.87/2.93  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 8.87/2.93  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 8.87/2.93  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 8.87/2.93  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.87/2.93  tff(f_62, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 8.87/2.93  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 8.87/2.93  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 8.87/2.93  tff(c_44, plain, (![A_33, B_34]: (v1_relat_1(k2_zfmisc_1(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.87/2.93  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.87/2.93  tff(c_95, plain, (![B_59, A_60]: (v1_relat_1(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.87/2.93  tff(c_101, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_95])).
% 8.87/2.93  tff(c_105, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_101])).
% 8.87/2.93  tff(c_176, plain, (![C_76, B_77, A_78]: (v5_relat_1(C_76, B_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.87/2.93  tff(c_185, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_176])).
% 8.87/2.93  tff(c_40, plain, (![B_31, A_30]: (r1_tarski(k2_relat_1(B_31), A_30) | ~v5_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.87/2.93  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.87/2.93  tff(c_131, plain, (![C_67, A_68, B_69]: (v4_relat_1(C_67, A_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.87/2.93  tff(c_140, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_131])).
% 8.87/2.93  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, k2_xboole_0(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.87/2.93  tff(c_36, plain, (![B_29, A_28]: (r1_tarski(k1_relat_1(B_29), A_28) | ~v4_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.87/2.93  tff(c_24, plain, (![A_18, B_19]: (r1_tarski(k1_zfmisc_1(A_18), k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.87/2.93  tff(c_12, plain, (![C_15, A_11]: (r2_hidden(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.87/2.93  tff(c_28, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.87/2.93  tff(c_252, plain, (![A_93, C_94, B_95]: (m1_subset_1(A_93, C_94) | ~m1_subset_1(B_95, k1_zfmisc_1(C_94)) | ~r2_hidden(A_93, B_95))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.87/2.93  tff(c_260, plain, (![A_97, B_98, A_99]: (m1_subset_1(A_97, B_98) | ~r2_hidden(A_97, A_99) | ~r1_tarski(A_99, B_98))), inference(resolution, [status(thm)], [c_28, c_252])).
% 8.87/2.93  tff(c_344, plain, (![C_118, B_119, A_120]: (m1_subset_1(C_118, B_119) | ~r1_tarski(k1_zfmisc_1(A_120), B_119) | ~r1_tarski(C_118, A_120))), inference(resolution, [status(thm)], [c_12, c_260])).
% 8.87/2.93  tff(c_361, plain, (![C_124, B_125, A_126]: (m1_subset_1(C_124, k1_zfmisc_1(B_125)) | ~r1_tarski(C_124, A_126) | ~r1_tarski(A_126, B_125))), inference(resolution, [status(thm)], [c_24, c_344])).
% 8.87/2.93  tff(c_6455, plain, (![B_808, B_809, A_810]: (m1_subset_1(k1_relat_1(B_808), k1_zfmisc_1(B_809)) | ~r1_tarski(A_810, B_809) | ~v4_relat_1(B_808, A_810) | ~v1_relat_1(B_808))), inference(resolution, [status(thm)], [c_36, c_361])).
% 8.87/2.93  tff(c_6637, plain, (![B_813, A_814, B_815]: (m1_subset_1(k1_relat_1(B_813), k1_zfmisc_1(k2_xboole_0(A_814, B_815))) | ~v4_relat_1(B_813, A_814) | ~v1_relat_1(B_813))), inference(resolution, [status(thm)], [c_4, c_6455])).
% 8.87/2.93  tff(c_26, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.87/2.93  tff(c_6652, plain, (![B_816, A_817, B_818]: (r1_tarski(k1_relat_1(B_816), k2_xboole_0(A_817, B_818)) | ~v4_relat_1(B_816, A_817) | ~v1_relat_1(B_816))), inference(resolution, [status(thm)], [c_6637, c_26])).
% 8.87/2.93  tff(c_42, plain, (![A_32]: (k2_xboole_0(k1_relat_1(A_32), k2_relat_1(A_32))=k3_relat_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.87/2.93  tff(c_267, plain, (![A_103, C_104, B_105]: (r1_tarski(k2_xboole_0(A_103, C_104), B_105) | ~r1_tarski(C_104, B_105) | ~r1_tarski(A_103, B_105))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.87/2.93  tff(c_803, plain, (![A_216, B_217]: (r1_tarski(k3_relat_1(A_216), B_217) | ~r1_tarski(k2_relat_1(A_216), B_217) | ~r1_tarski(k1_relat_1(A_216), B_217) | ~v1_relat_1(A_216))), inference(superposition, [status(thm), theory('equality')], [c_42, c_267])).
% 8.87/2.93  tff(c_50, plain, (~r1_tarski(k3_relat_1('#skF_5'), k2_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.87/2.93  tff(c_829, plain, (~r1_tarski(k2_relat_1('#skF_5'), k2_xboole_0('#skF_3', '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), k2_xboole_0('#skF_3', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_803, c_50])).
% 8.87/2.93  tff(c_841, plain, (~r1_tarski(k2_relat_1('#skF_5'), k2_xboole_0('#skF_3', '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), k2_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_829])).
% 8.87/2.93  tff(c_849, plain, (~r1_tarski(k1_relat_1('#skF_5'), k2_xboole_0('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_841])).
% 8.87/2.93  tff(c_6674, plain, (~v4_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6652, c_849])).
% 8.87/2.93  tff(c_6698, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_140, c_6674])).
% 8.87/2.93  tff(c_6699, plain, (~r1_tarski(k2_relat_1('#skF_5'), k2_xboole_0('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_841])).
% 8.87/2.93  tff(c_6710, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_2, c_6699])).
% 8.87/2.93  tff(c_6713, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_6710])).
% 8.87/2.93  tff(c_6717, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_185, c_6713])).
% 8.87/2.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.87/2.93  
% 8.87/2.93  Inference rules
% 8.87/2.93  ----------------------
% 8.87/2.93  #Ref     : 0
% 8.87/2.93  #Sup     : 1648
% 8.87/2.93  #Fact    : 0
% 8.87/2.93  #Define  : 0
% 8.87/2.93  #Split   : 11
% 8.87/2.93  #Chain   : 0
% 8.87/2.93  #Close   : 0
% 8.87/2.93  
% 8.87/2.93  Ordering : KBO
% 8.87/2.93  
% 8.87/2.93  Simplification rules
% 8.87/2.93  ----------------------
% 8.87/2.93  #Subsume      : 204
% 8.87/2.93  #Demod        : 118
% 8.87/2.93  #Tautology    : 64
% 8.87/2.93  #SimpNegUnit  : 18
% 8.87/2.93  #BackRed      : 0
% 8.87/2.93  
% 8.87/2.93  #Partial instantiations: 0
% 8.87/2.93  #Strategies tried      : 1
% 8.87/2.93  
% 8.87/2.93  Timing (in seconds)
% 8.87/2.93  ----------------------
% 8.87/2.94  Preprocessing        : 0.31
% 8.87/2.94  Parsing              : 0.16
% 8.87/2.94  CNF conversion       : 0.02
% 8.87/2.94  Main loop            : 1.87
% 8.87/2.94  Inferencing          : 0.55
% 8.87/2.94  Reduction            : 0.55
% 8.87/2.94  Demodulation         : 0.38
% 9.03/2.94  BG Simplification    : 0.06
% 9.03/2.94  Subsumption          : 0.55
% 9.03/2.94  Abstraction          : 0.07
% 9.03/2.94  MUC search           : 0.00
% 9.03/2.94  Cooper               : 0.00
% 9.03/2.94  Total                : 2.21
% 9.03/2.94  Index Insertion      : 0.00
% 9.03/2.94  Index Deletion       : 0.00
% 9.03/2.94  Index Matching       : 0.00
% 9.04/2.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
