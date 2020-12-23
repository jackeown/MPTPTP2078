%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:10 EST 2020

% Result     : Theorem 8.59s
% Output     : CNFRefutation 8.77s
% Verified   : 
% Statistics : Number of formulae       :  252 (2227 expanded)
%              Number of leaves         :   44 ( 726 expanded)
%              Depth                    :   14
%              Number of atoms          :  434 (6144 expanded)
%              Number of equality atoms :  164 (2104 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_158,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_138,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_120,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_34,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_10837,plain,(
    ! [B_1007,A_1008] :
      ( v1_relat_1(B_1007)
      | ~ m1_subset_1(B_1007,k1_zfmisc_1(A_1008))
      | ~ v1_relat_1(A_1008) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10843,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_74,c_10837])).

tff(c_10847,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10843])).

tff(c_11075,plain,(
    ! [C_1044,A_1045,B_1046] :
      ( v4_relat_1(C_1044,A_1045)
      | ~ m1_subset_1(C_1044,k1_zfmisc_1(k2_zfmisc_1(A_1045,B_1046))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_11090,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_11075])).

tff(c_30,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_11305,plain,(
    ! [A_1088,B_1089,C_1090] :
      ( k2_relset_1(A_1088,B_1089,C_1090) = k2_relat_1(C_1090)
      | ~ m1_subset_1(C_1090,k1_zfmisc_1(k2_zfmisc_1(A_1088,B_1089))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_11320,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_11305])).

tff(c_72,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_11329,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11320,c_72])).

tff(c_11385,plain,(
    ! [C_1099,A_1100,B_1101] :
      ( m1_subset_1(C_1099,k1_zfmisc_1(k2_zfmisc_1(A_1100,B_1101)))
      | ~ r1_tarski(k2_relat_1(C_1099),B_1101)
      | ~ r1_tarski(k1_relat_1(C_1099),A_1100)
      | ~ v1_relat_1(C_1099) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_70,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_101,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_76,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_630,plain,(
    ! [A_132,B_133,C_134] :
      ( k1_relset_1(A_132,B_133,C_134) = k1_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_645,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_630])).

tff(c_769,plain,(
    ! [B_159,A_160,C_161] :
      ( k1_xboole_0 = B_159
      | k1_relset_1(A_160,B_159,C_161) = A_160
      | ~ v1_funct_2(C_161,A_160,B_159)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_779,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_769])).

tff(c_790,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_645,c_779])).

tff(c_791,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_790])).

tff(c_217,plain,(
    ! [B_69,A_70] :
      ( v1_relat_1(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70))
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_223,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_74,c_217])).

tff(c_227,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_223])).

tff(c_596,plain,(
    ! [A_129,B_130,C_131] :
      ( k2_relset_1(A_129,B_130,C_131) = k2_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_611,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_596])).

tff(c_613,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_72])).

tff(c_662,plain,(
    ! [C_140,A_141,B_142] :
      ( m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ r1_tarski(k2_relat_1(C_140),B_142)
      | ~ r1_tarski(k1_relat_1(C_140),A_141)
      | ~ v1_relat_1(C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2892,plain,(
    ! [C_308,A_309,B_310] :
      ( r1_tarski(C_308,k2_zfmisc_1(A_309,B_310))
      | ~ r1_tarski(k2_relat_1(C_308),B_310)
      | ~ r1_tarski(k1_relat_1(C_308),A_309)
      | ~ v1_relat_1(C_308) ) ),
    inference(resolution,[status(thm)],[c_662,c_20])).

tff(c_2896,plain,(
    ! [A_309] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_309,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_309)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_613,c_2892])).

tff(c_2985,plain,(
    ! [A_312] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_312,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_312) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_791,c_2896])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_644,plain,(
    ! [A_132,B_133,A_7] :
      ( k1_relset_1(A_132,B_133,A_7) = k1_relat_1(A_7)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_132,B_133)) ) ),
    inference(resolution,[status(thm)],[c_22,c_630])).

tff(c_2991,plain,(
    ! [A_312] :
      ( k1_relset_1(A_312,'#skF_4','#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',A_312) ) ),
    inference(resolution,[status(thm)],[c_2985,c_644])).

tff(c_3057,plain,(
    ! [A_315] :
      ( k1_relset_1(A_315,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_315) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_791,c_2991])).

tff(c_3062,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_3057])).

tff(c_238,plain,(
    ! [A_71,B_72] :
      ( v1_relat_1(A_71)
      | ~ v1_relat_1(B_72)
      | ~ r1_tarski(A_71,B_72) ) ),
    inference(resolution,[status(thm)],[c_22,c_217])).

tff(c_254,plain,
    ( v1_relat_1(k2_relset_1('#skF_2','#skF_3','#skF_5'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_238])).

tff(c_287,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_2904,plain,(
    ! [A_309] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_309,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_309) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_791,c_2896])).

tff(c_937,plain,(
    ! [B_175,C_176,A_177] :
      ( k1_xboole_0 = B_175
      | v1_funct_2(C_176,A_177,B_175)
      | k1_relset_1(A_177,B_175,C_176) != A_177
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_177,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_3515,plain,(
    ! [B_333,A_334,A_335] :
      ( k1_xboole_0 = B_333
      | v1_funct_2(A_334,A_335,B_333)
      | k1_relset_1(A_335,B_333,A_334) != A_335
      | ~ r1_tarski(A_334,k2_zfmisc_1(A_335,B_333)) ) ),
    inference(resolution,[status(thm)],[c_22,c_937])).

tff(c_3543,plain,(
    ! [A_309] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_5',A_309,'#skF_4')
      | k1_relset_1(A_309,'#skF_4','#skF_5') != A_309
      | ~ r1_tarski('#skF_2',A_309) ) ),
    inference(resolution,[status(thm)],[c_2904,c_3515])).

tff(c_3642,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3543])).

tff(c_18,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_117,plain,(
    ! [A_55,B_56] : v1_relat_1(k2_zfmisc_1(A_55,B_56)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_119,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_117])).

tff(c_3719,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3642,c_119])).

tff(c_3727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_3719])).

tff(c_3887,plain,(
    ! [A_348] :
      ( v1_funct_2('#skF_5',A_348,'#skF_4')
      | k1_relset_1(A_348,'#skF_4','#skF_5') != A_348
      | ~ r1_tarski('#skF_2',A_348) ) ),
    inference(splitRight,[status(thm)],[c_3543])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_68,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_80,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_68])).

tff(c_147,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_3893,plain,
    ( k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_3887,c_147])).

tff(c_3898,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3062,c_3893])).

tff(c_3900,plain,(
    v1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_38,plain,(
    ! [A_20] :
      ( k1_relat_1(A_20) != k1_xboole_0
      | k1_xboole_0 = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3908,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3900,c_38])).

tff(c_3918,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3908])).

tff(c_4401,plain,(
    ! [A_430,B_431,C_432] :
      ( k1_relset_1(A_430,B_431,C_432) = k1_relat_1(C_432)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(A_430,B_431))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4416,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_4401])).

tff(c_4948,plain,(
    ! [B_477,A_478,C_479] :
      ( k1_xboole_0 = B_477
      | k1_relset_1(A_478,B_477,C_479) = A_478
      | ~ v1_funct_2(C_479,A_478,B_477)
      | ~ m1_subset_1(C_479,k1_zfmisc_1(k2_zfmisc_1(A_478,B_477))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4961,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_4948])).

tff(c_4972,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4416,c_4961])).

tff(c_4973,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_4972])).

tff(c_4304,plain,(
    ! [A_415,B_416,C_417] :
      ( k2_relset_1(A_415,B_416,C_417) = k2_relat_1(C_417)
      | ~ m1_subset_1(C_417,k1_zfmisc_1(k2_zfmisc_1(A_415,B_416))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4319,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_4304])).

tff(c_4324,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4319,c_72])).

tff(c_4451,plain,(
    ! [C_436,A_437,B_438] :
      ( m1_subset_1(C_436,k1_zfmisc_1(k2_zfmisc_1(A_437,B_438)))
      | ~ r1_tarski(k2_relat_1(C_436),B_438)
      | ~ r1_tarski(k1_relat_1(C_436),A_437)
      | ~ v1_relat_1(C_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6571,plain,(
    ! [C_582,A_583,B_584] :
      ( r1_tarski(C_582,k2_zfmisc_1(A_583,B_584))
      | ~ r1_tarski(k2_relat_1(C_582),B_584)
      | ~ r1_tarski(k1_relat_1(C_582),A_583)
      | ~ v1_relat_1(C_582) ) ),
    inference(resolution,[status(thm)],[c_4451,c_20])).

tff(c_6575,plain,(
    ! [A_583] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_583,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_583)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4324,c_6571])).

tff(c_6585,plain,(
    ! [A_585] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_585,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_585) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_4973,c_6575])).

tff(c_4415,plain,(
    ! [A_430,B_431,A_7] :
      ( k1_relset_1(A_430,B_431,A_7) = k1_relat_1(A_7)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_430,B_431)) ) ),
    inference(resolution,[status(thm)],[c_22,c_4401])).

tff(c_6588,plain,(
    ! [A_585] :
      ( k1_relset_1(A_585,'#skF_4','#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',A_585) ) ),
    inference(resolution,[status(thm)],[c_6585,c_4415])).

tff(c_6647,plain,(
    ! [A_587] :
      ( k1_relset_1(A_587,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_587) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4973,c_6588])).

tff(c_6652,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_6647])).

tff(c_50,plain,(
    ! [A_33] :
      ( r2_hidden('#skF_1'(A_33),A_33)
      | k1_xboole_0 = A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4138,plain,(
    ! [C_384,B_385,A_386] :
      ( ~ v1_xboole_0(C_384)
      | ~ m1_subset_1(B_385,k1_zfmisc_1(C_384))
      | ~ r2_hidden(A_386,B_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4188,plain,(
    ! [B_389,A_390,A_391] :
      ( ~ v1_xboole_0(B_389)
      | ~ r2_hidden(A_390,A_391)
      | ~ r1_tarski(A_391,B_389) ) ),
    inference(resolution,[status(thm)],[c_22,c_4138])).

tff(c_4192,plain,(
    ! [B_392,A_393] :
      ( ~ v1_xboole_0(B_392)
      | ~ r1_tarski(A_393,B_392)
      | k1_xboole_0 = A_393 ) ),
    inference(resolution,[status(thm)],[c_50,c_4188])).

tff(c_4210,plain,
    ( ~ v1_xboole_0('#skF_4')
    | k2_relset_1('#skF_2','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_4192])).

tff(c_4214,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4210])).

tff(c_6583,plain,(
    ! [A_583] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_583,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_583) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_4973,c_6575])).

tff(c_7212,plain,(
    ! [B_611,A_612,A_613] :
      ( k1_xboole_0 = B_611
      | k1_relset_1(A_612,B_611,A_613) = A_612
      | ~ v1_funct_2(A_613,A_612,B_611)
      | ~ r1_tarski(A_613,k2_zfmisc_1(A_612,B_611)) ) ),
    inference(resolution,[status(thm)],[c_22,c_4948])).

tff(c_7240,plain,(
    ! [A_583] :
      ( k1_xboole_0 = '#skF_4'
      | k1_relset_1(A_583,'#skF_4','#skF_5') = A_583
      | ~ v1_funct_2('#skF_5',A_583,'#skF_4')
      | ~ r1_tarski('#skF_2',A_583) ) ),
    inference(resolution,[status(thm)],[c_6583,c_7212])).

tff(c_7320,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_7240])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_7409,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7320,c_2])).

tff(c_7412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4214,c_7409])).

tff(c_7414,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7240])).

tff(c_4767,plain,(
    ! [B_467,C_468,A_469] :
      ( k1_xboole_0 = B_467
      | v1_funct_2(C_468,A_469,B_467)
      | k1_relset_1(A_469,B_467,C_468) != A_469
      | ~ m1_subset_1(C_468,k1_zfmisc_1(k2_zfmisc_1(A_469,B_467))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_6879,plain,(
    ! [B_594,A_595,A_596] :
      ( k1_xboole_0 = B_594
      | v1_funct_2(A_595,A_596,B_594)
      | k1_relset_1(A_596,B_594,A_595) != A_596
      | ~ r1_tarski(A_595,k2_zfmisc_1(A_596,B_594)) ) ),
    inference(resolution,[status(thm)],[c_22,c_4767])).

tff(c_6907,plain,(
    ! [A_583] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_5',A_583,'#skF_4')
      | k1_relset_1(A_583,'#skF_4','#skF_5') != A_583
      | ~ r1_tarski('#skF_2',A_583) ) ),
    inference(resolution,[status(thm)],[c_6583,c_6879])).

tff(c_7666,plain,(
    ! [A_629] :
      ( v1_funct_2('#skF_5',A_629,'#skF_4')
      | k1_relset_1(A_629,'#skF_4','#skF_5') != A_629
      | ~ r1_tarski('#skF_2',A_629) ) ),
    inference(negUnitSimplification,[status(thm)],[c_7414,c_6907])).

tff(c_7672,plain,
    ( k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_7666,c_147])).

tff(c_7677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6652,c_7672])).

tff(c_7679,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_4210])).

tff(c_123,plain,(
    ! [A_57] :
      ( v1_xboole_0(k1_relat_1(A_57))
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_127,plain,(
    ! [A_57] :
      ( k1_relat_1(A_57) = k1_xboole_0
      | ~ v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_123,c_4])).

tff(c_7682,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7679,c_127])).

tff(c_7689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3918,c_7682])).

tff(c_7690,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3908])).

tff(c_36,plain,(
    ! [A_20] :
      ( k2_relat_1(A_20) != k1_xboole_0
      | k1_xboole_0 = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_234,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_227,c_36])).

tff(c_236,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_7695,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7690,c_236])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7708,plain,(
    ! [A_4] : r1_tarski('#skF_4',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7690,c_12])).

tff(c_258,plain,(
    ! [B_73,A_74] :
      ( B_73 = A_74
      | ~ r1_tarski(B_73,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_268,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_72,c_258])).

tff(c_7746,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7708,c_268])).

tff(c_8237,plain,(
    ! [A_707,B_708,C_709] :
      ( k2_relset_1(A_707,B_708,C_709) = k2_relat_1(C_709)
      | ~ m1_subset_1(C_709,k1_zfmisc_1(k2_zfmisc_1(A_707,B_708))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_8250,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_8237])).

tff(c_8253,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7746,c_8250])).

tff(c_8255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7695,c_8253])).

tff(c_8256,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_8267,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8256,c_101])).

tff(c_129,plain,(
    ! [A_59] :
      ( k1_relat_1(A_59) = k1_xboole_0
      | ~ v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_123,c_4])).

tff(c_137,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_129])).

tff(c_8262,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8256,c_8256,c_137])).

tff(c_8713,plain,(
    ! [A_776,B_777,C_778] :
      ( k1_relset_1(A_776,B_777,C_778) = k1_relat_1(C_778)
      | ~ m1_subset_1(C_778,k1_zfmisc_1(k2_zfmisc_1(A_776,B_777))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_8726,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_8713])).

tff(c_8729,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8262,c_8726])).

tff(c_66,plain,(
    ! [B_48,A_47,C_49] :
      ( k1_xboole_0 = B_48
      | k1_relset_1(A_47,B_48,C_49) = A_47
      | ~ v1_funct_2(C_49,A_47,B_48)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_9177,plain,(
    ! [B_836,A_837,C_838] :
      ( B_836 = '#skF_5'
      | k1_relset_1(A_837,B_836,C_838) = A_837
      | ~ v1_funct_2(C_838,A_837,B_836)
      | ~ m1_subset_1(C_838,k1_zfmisc_1(k2_zfmisc_1(A_837,B_836))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8256,c_66])).

tff(c_9193,plain,
    ( '#skF_5' = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_9177])).

tff(c_9199,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_8729,c_9193])).

tff(c_9200,plain,(
    '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_8267,c_9199])).

tff(c_8271,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8256,c_2])).

tff(c_9255,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9200,c_8271])).

tff(c_8266,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_5',B_6) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8256,c_8256,c_18])).

tff(c_9251,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_2',B_6) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9200,c_9200,c_8266])).

tff(c_8370,plain,(
    ! [C_718,B_719,A_720] :
      ( ~ v1_xboole_0(C_718)
      | ~ m1_subset_1(B_719,k1_zfmisc_1(C_718))
      | ~ r2_hidden(A_720,B_719) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8376,plain,(
    ! [A_720] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_720,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_8370])).

tff(c_8404,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_8376])).

tff(c_9349,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9251,c_8404])).

tff(c_9352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9255,c_9349])).

tff(c_9354,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_8376])).

tff(c_8269,plain,(
    ! [A_1] :
      ( A_1 = '#skF_5'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8256,c_4])).

tff(c_9385,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_9354,c_8269])).

tff(c_14,plain,(
    ! [B_6,A_5] :
      ( k1_xboole_0 = B_6
      | k1_xboole_0 = A_5
      | k2_zfmisc_1(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_9660,plain,(
    ! [B_893,A_894] :
      ( B_893 = '#skF_5'
      | A_894 = '#skF_5'
      | k2_zfmisc_1(A_894,B_893) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8256,c_8256,c_8256,c_14])).

tff(c_9663,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_9385,c_9660])).

tff(c_9672,plain,(
    '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_8267,c_9663])).

tff(c_9699,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9672,c_9672,c_8262])).

tff(c_8270,plain,(
    ! [A_4] : r1_tarski('#skF_5',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8256,c_12])).

tff(c_9701,plain,(
    ! [A_4] : r1_tarski('#skF_2',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9672,c_8270])).

tff(c_10154,plain,(
    ! [A_937,B_938,C_939] :
      ( k1_relset_1(A_937,B_938,C_939) = k1_relat_1(C_939)
      | ~ m1_subset_1(C_939,k1_zfmisc_1(k2_zfmisc_1(A_937,B_938))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10741,plain,(
    ! [A_997,B_998,A_999] :
      ( k1_relset_1(A_997,B_998,A_999) = k1_relat_1(A_999)
      | ~ r1_tarski(A_999,k2_zfmisc_1(A_997,B_998)) ) ),
    inference(resolution,[status(thm)],[c_22,c_10154])).

tff(c_10754,plain,(
    ! [A_997,B_998] : k1_relset_1(A_997,B_998,'#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_9701,c_10741])).

tff(c_10764,plain,(
    ! [A_997,B_998] : k1_relset_1(A_997,B_998,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9699,c_10754])).

tff(c_9704,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9672,c_8256])).

tff(c_16,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_56,plain,(
    ! [A_47] :
      ( v1_funct_2(k1_xboole_0,A_47,k1_xboole_0)
      | k1_xboole_0 = A_47
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_47,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_84,plain,(
    ! [A_47] :
      ( v1_funct_2(k1_xboole_0,A_47,k1_xboole_0)
      | k1_xboole_0 = A_47
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_56])).

tff(c_9714,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_9726,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9704,c_9704,c_9714])).

tff(c_9729,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_9726])).

tff(c_9733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_9729])).

tff(c_9735,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_9747,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9704,c_9704,c_9735])).

tff(c_60,plain,(
    ! [C_49,B_48] :
      ( v1_funct_2(C_49,k1_xboole_0,B_48)
      | k1_relset_1(k1_xboole_0,B_48,C_49) != k1_xboole_0
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_82,plain,(
    ! [C_49,B_48] :
      ( v1_funct_2(C_49,k1_xboole_0,B_48)
      | k1_relset_1(k1_xboole_0,B_48,C_49) != k1_xboole_0
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_60])).

tff(c_10250,plain,(
    ! [C_954,B_955] :
      ( v1_funct_2(C_954,'#skF_2',B_955)
      | k1_relset_1('#skF_2',B_955,C_954) != '#skF_2'
      | ~ m1_subset_1(C_954,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9704,c_9704,c_9704,c_9704,c_82])).

tff(c_10276,plain,(
    ! [B_959] :
      ( v1_funct_2('#skF_2','#skF_2',B_959)
      | k1_relset_1('#skF_2',B_959,'#skF_2') != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_9747,c_10250])).

tff(c_9706,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9672,c_147])).

tff(c_10287,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_2') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_10276,c_9706])).

tff(c_10772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10764,c_10287])).

tff(c_10773,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_11408,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_11385,c_10773])).

tff(c_11426,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10847,c_11329,c_11408])).

tff(c_11429,plain,
    ( ~ v4_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_11426])).

tff(c_11433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10847,c_11090,c_11429])).

tff(c_11435,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_11434,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_11444,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11435,c_11434])).

tff(c_11439,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11434,c_2])).

tff(c_11449,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11444,c_11439])).

tff(c_11495,plain,(
    ! [A_1108] :
      ( v1_xboole_0(k1_relat_1(A_1108))
      | ~ v1_xboole_0(A_1108) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_11437,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11434,c_4])).

tff(c_11458,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11444,c_11437])).

tff(c_11501,plain,(
    ! [A_1109] :
      ( k1_relat_1(A_1109) = '#skF_3'
      | ~ v1_xboole_0(A_1109) ) ),
    inference(resolution,[status(thm)],[c_11495,c_11458])).

tff(c_11509,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_11449,c_11501])).

tff(c_11438,plain,(
    ! [A_4] : r1_tarski('#skF_2',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11434,c_12])).

tff(c_11455,plain,(
    ! [A_4] : r1_tarski('#skF_3',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11444,c_11438])).

tff(c_12324,plain,(
    ! [A_1222,B_1223,C_1224] :
      ( k1_relset_1(A_1222,B_1223,C_1224) = k1_relat_1(C_1224)
      | ~ m1_subset_1(C_1224,k1_zfmisc_1(k2_zfmisc_1(A_1222,B_1223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_12526,plain,(
    ! [A_1247,B_1248,A_1249] :
      ( k1_relset_1(A_1247,B_1248,A_1249) = k1_relat_1(A_1249)
      | ~ r1_tarski(A_1249,k2_zfmisc_1(A_1247,B_1248)) ) ),
    inference(resolution,[status(thm)],[c_22,c_12324])).

tff(c_12543,plain,(
    ! [A_1247,B_1248] : k1_relset_1(A_1247,B_1248,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_11455,c_12526])).

tff(c_12550,plain,(
    ! [A_1247,B_1248] : k1_relset_1(A_1247,B_1248,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11509,c_12543])).

tff(c_11466,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_3',B_6) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11435,c_11435,c_18])).

tff(c_11500,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11466,c_11444,c_74])).

tff(c_11574,plain,(
    ! [A_1116,B_1117] :
      ( r1_tarski(A_1116,B_1117)
      | ~ m1_subset_1(A_1116,k1_zfmisc_1(B_1117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_11582,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_11500,c_11574])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11597,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_11582,c_6])).

tff(c_11600,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11455,c_11597])).

tff(c_11603,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11600,c_11500])).

tff(c_12935,plain,(
    ! [C_1277,B_1278] :
      ( v1_funct_2(C_1277,'#skF_3',B_1278)
      | k1_relset_1('#skF_3',B_1278,C_1277) != '#skF_3'
      | ~ m1_subset_1(C_1277,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11435,c_11435,c_11435,c_11435,c_82])).

tff(c_12937,plain,(
    ! [B_1278] :
      ( v1_funct_2('#skF_3','#skF_3',B_1278)
      | k1_relset_1('#skF_3',B_1278,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_11603,c_12935])).

tff(c_12943,plain,(
    ! [B_1278] : v1_funct_2('#skF_3','#skF_3',B_1278) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12550,c_12937])).

tff(c_11522,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11444,c_11500,c_11466,c_11444,c_80])).

tff(c_11602,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11600,c_11522])).

tff(c_12948,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12943,c_11602])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.59/2.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.59/2.99  
% 8.59/2.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.59/2.99  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 8.59/2.99  
% 8.59/2.99  %Foreground sorts:
% 8.59/2.99  
% 8.59/2.99  
% 8.59/2.99  %Background operators:
% 8.59/2.99  
% 8.59/2.99  
% 8.59/2.99  %Foreground operators:
% 8.59/2.99  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.59/2.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.59/2.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.59/2.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.59/2.99  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.59/2.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.59/2.99  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 8.59/2.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.59/2.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.59/2.99  tff('#skF_5', type, '#skF_5': $i).
% 8.59/2.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.59/2.99  tff('#skF_2', type, '#skF_2': $i).
% 8.59/2.99  tff('#skF_3', type, '#skF_3': $i).
% 8.59/2.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.59/2.99  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.59/2.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.59/2.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.59/2.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.59/2.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.59/2.99  tff('#skF_4', type, '#skF_4': $i).
% 8.59/2.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.59/2.99  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.59/2.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.59/2.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.59/2.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.59/2.99  
% 8.77/3.02  tff(f_74, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.77/3.02  tff(f_158, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 8.77/3.02  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.77/3.02  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.77/3.02  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 8.77/3.02  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.77/3.02  tff(f_104, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 8.77/3.02  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.77/3.02  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.77/3.02  tff(f_138, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.77/3.02  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.77/3.02  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.77/3.02  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 8.77/3.02  tff(f_120, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 8.77/3.02  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 8.77/3.02  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.77/3.02  tff(f_72, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 8.77/3.02  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.77/3.02  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.77/3.02  tff(c_34, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.77/3.02  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.77/3.02  tff(c_10837, plain, (![B_1007, A_1008]: (v1_relat_1(B_1007) | ~m1_subset_1(B_1007, k1_zfmisc_1(A_1008)) | ~v1_relat_1(A_1008))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.77/3.02  tff(c_10843, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_74, c_10837])).
% 8.77/3.02  tff(c_10847, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_10843])).
% 8.77/3.02  tff(c_11075, plain, (![C_1044, A_1045, B_1046]: (v4_relat_1(C_1044, A_1045) | ~m1_subset_1(C_1044, k1_zfmisc_1(k2_zfmisc_1(A_1045, B_1046))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.77/3.02  tff(c_11090, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_11075])).
% 8.77/3.02  tff(c_30, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.77/3.02  tff(c_11305, plain, (![A_1088, B_1089, C_1090]: (k2_relset_1(A_1088, B_1089, C_1090)=k2_relat_1(C_1090) | ~m1_subset_1(C_1090, k1_zfmisc_1(k2_zfmisc_1(A_1088, B_1089))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.77/3.02  tff(c_11320, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_11305])).
% 8.77/3.02  tff(c_72, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.77/3.02  tff(c_11329, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11320, c_72])).
% 8.77/3.02  tff(c_11385, plain, (![C_1099, A_1100, B_1101]: (m1_subset_1(C_1099, k1_zfmisc_1(k2_zfmisc_1(A_1100, B_1101))) | ~r1_tarski(k2_relat_1(C_1099), B_1101) | ~r1_tarski(k1_relat_1(C_1099), A_1100) | ~v1_relat_1(C_1099))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.77/3.02  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.77/3.02  tff(c_70, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.77/3.02  tff(c_101, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_70])).
% 8.77/3.02  tff(c_76, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.77/3.02  tff(c_630, plain, (![A_132, B_133, C_134]: (k1_relset_1(A_132, B_133, C_134)=k1_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.77/3.02  tff(c_645, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_630])).
% 8.77/3.02  tff(c_769, plain, (![B_159, A_160, C_161]: (k1_xboole_0=B_159 | k1_relset_1(A_160, B_159, C_161)=A_160 | ~v1_funct_2(C_161, A_160, B_159) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.77/3.02  tff(c_779, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_769])).
% 8.77/3.02  tff(c_790, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_645, c_779])).
% 8.77/3.02  tff(c_791, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_101, c_790])).
% 8.77/3.02  tff(c_217, plain, (![B_69, A_70]: (v1_relat_1(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.77/3.02  tff(c_223, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_74, c_217])).
% 8.77/3.02  tff(c_227, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_223])).
% 8.77/3.02  tff(c_596, plain, (![A_129, B_130, C_131]: (k2_relset_1(A_129, B_130, C_131)=k2_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.77/3.02  tff(c_611, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_596])).
% 8.77/3.02  tff(c_613, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_611, c_72])).
% 8.77/3.03  tff(c_662, plain, (![C_140, A_141, B_142]: (m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | ~r1_tarski(k2_relat_1(C_140), B_142) | ~r1_tarski(k1_relat_1(C_140), A_141) | ~v1_relat_1(C_140))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.77/3.03  tff(c_20, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.77/3.03  tff(c_2892, plain, (![C_308, A_309, B_310]: (r1_tarski(C_308, k2_zfmisc_1(A_309, B_310)) | ~r1_tarski(k2_relat_1(C_308), B_310) | ~r1_tarski(k1_relat_1(C_308), A_309) | ~v1_relat_1(C_308))), inference(resolution, [status(thm)], [c_662, c_20])).
% 8.77/3.03  tff(c_2896, plain, (![A_309]: (r1_tarski('#skF_5', k2_zfmisc_1(A_309, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), A_309) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_613, c_2892])).
% 8.77/3.03  tff(c_2985, plain, (![A_312]: (r1_tarski('#skF_5', k2_zfmisc_1(A_312, '#skF_4')) | ~r1_tarski('#skF_2', A_312))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_791, c_2896])).
% 8.77/3.03  tff(c_22, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.77/3.03  tff(c_644, plain, (![A_132, B_133, A_7]: (k1_relset_1(A_132, B_133, A_7)=k1_relat_1(A_7) | ~r1_tarski(A_7, k2_zfmisc_1(A_132, B_133)))), inference(resolution, [status(thm)], [c_22, c_630])).
% 8.77/3.03  tff(c_2991, plain, (![A_312]: (k1_relset_1(A_312, '#skF_4', '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_2', A_312))), inference(resolution, [status(thm)], [c_2985, c_644])).
% 8.77/3.03  tff(c_3057, plain, (![A_315]: (k1_relset_1(A_315, '#skF_4', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_315))), inference(demodulation, [status(thm), theory('equality')], [c_791, c_2991])).
% 8.77/3.03  tff(c_3062, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_10, c_3057])).
% 8.77/3.03  tff(c_238, plain, (![A_71, B_72]: (v1_relat_1(A_71) | ~v1_relat_1(B_72) | ~r1_tarski(A_71, B_72))), inference(resolution, [status(thm)], [c_22, c_217])).
% 8.77/3.03  tff(c_254, plain, (v1_relat_1(k2_relset_1('#skF_2', '#skF_3', '#skF_5')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_238])).
% 8.77/3.03  tff(c_287, plain, (~v1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_254])).
% 8.77/3.03  tff(c_2904, plain, (![A_309]: (r1_tarski('#skF_5', k2_zfmisc_1(A_309, '#skF_4')) | ~r1_tarski('#skF_2', A_309))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_791, c_2896])).
% 8.77/3.03  tff(c_937, plain, (![B_175, C_176, A_177]: (k1_xboole_0=B_175 | v1_funct_2(C_176, A_177, B_175) | k1_relset_1(A_177, B_175, C_176)!=A_177 | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_177, B_175))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.77/3.03  tff(c_3515, plain, (![B_333, A_334, A_335]: (k1_xboole_0=B_333 | v1_funct_2(A_334, A_335, B_333) | k1_relset_1(A_335, B_333, A_334)!=A_335 | ~r1_tarski(A_334, k2_zfmisc_1(A_335, B_333)))), inference(resolution, [status(thm)], [c_22, c_937])).
% 8.77/3.03  tff(c_3543, plain, (![A_309]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', A_309, '#skF_4') | k1_relset_1(A_309, '#skF_4', '#skF_5')!=A_309 | ~r1_tarski('#skF_2', A_309))), inference(resolution, [status(thm)], [c_2904, c_3515])).
% 8.77/3.03  tff(c_3642, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_3543])).
% 8.77/3.03  tff(c_18, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.77/3.03  tff(c_117, plain, (![A_55, B_56]: (v1_relat_1(k2_zfmisc_1(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.77/3.03  tff(c_119, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_117])).
% 8.77/3.03  tff(c_3719, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3642, c_119])).
% 8.77/3.03  tff(c_3727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_287, c_3719])).
% 8.77/3.03  tff(c_3887, plain, (![A_348]: (v1_funct_2('#skF_5', A_348, '#skF_4') | k1_relset_1(A_348, '#skF_4', '#skF_5')!=A_348 | ~r1_tarski('#skF_2', A_348))), inference(splitRight, [status(thm)], [c_3543])).
% 8.77/3.03  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.77/3.03  tff(c_68, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.77/3.03  tff(c_80, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_68])).
% 8.77/3.03  tff(c_147, plain, (~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_80])).
% 8.77/3.03  tff(c_3893, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_3887, c_147])).
% 8.77/3.03  tff(c_3898, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_3062, c_3893])).
% 8.77/3.03  tff(c_3900, plain, (v1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_254])).
% 8.77/3.03  tff(c_38, plain, (![A_20]: (k1_relat_1(A_20)!=k1_xboole_0 | k1_xboole_0=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.77/3.03  tff(c_3908, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_3900, c_38])).
% 8.77/3.03  tff(c_3918, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3908])).
% 8.77/3.03  tff(c_4401, plain, (![A_430, B_431, C_432]: (k1_relset_1(A_430, B_431, C_432)=k1_relat_1(C_432) | ~m1_subset_1(C_432, k1_zfmisc_1(k2_zfmisc_1(A_430, B_431))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.77/3.03  tff(c_4416, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_4401])).
% 8.77/3.03  tff(c_4948, plain, (![B_477, A_478, C_479]: (k1_xboole_0=B_477 | k1_relset_1(A_478, B_477, C_479)=A_478 | ~v1_funct_2(C_479, A_478, B_477) | ~m1_subset_1(C_479, k1_zfmisc_1(k2_zfmisc_1(A_478, B_477))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.77/3.03  tff(c_4961, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_4948])).
% 8.77/3.03  tff(c_4972, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_4416, c_4961])).
% 8.77/3.03  tff(c_4973, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_101, c_4972])).
% 8.77/3.03  tff(c_4304, plain, (![A_415, B_416, C_417]: (k2_relset_1(A_415, B_416, C_417)=k2_relat_1(C_417) | ~m1_subset_1(C_417, k1_zfmisc_1(k2_zfmisc_1(A_415, B_416))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.77/3.03  tff(c_4319, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_4304])).
% 8.77/3.03  tff(c_4324, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4319, c_72])).
% 8.77/3.03  tff(c_4451, plain, (![C_436, A_437, B_438]: (m1_subset_1(C_436, k1_zfmisc_1(k2_zfmisc_1(A_437, B_438))) | ~r1_tarski(k2_relat_1(C_436), B_438) | ~r1_tarski(k1_relat_1(C_436), A_437) | ~v1_relat_1(C_436))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.77/3.03  tff(c_6571, plain, (![C_582, A_583, B_584]: (r1_tarski(C_582, k2_zfmisc_1(A_583, B_584)) | ~r1_tarski(k2_relat_1(C_582), B_584) | ~r1_tarski(k1_relat_1(C_582), A_583) | ~v1_relat_1(C_582))), inference(resolution, [status(thm)], [c_4451, c_20])).
% 8.77/3.03  tff(c_6575, plain, (![A_583]: (r1_tarski('#skF_5', k2_zfmisc_1(A_583, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), A_583) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_4324, c_6571])).
% 8.77/3.03  tff(c_6585, plain, (![A_585]: (r1_tarski('#skF_5', k2_zfmisc_1(A_585, '#skF_4')) | ~r1_tarski('#skF_2', A_585))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_4973, c_6575])).
% 8.77/3.03  tff(c_4415, plain, (![A_430, B_431, A_7]: (k1_relset_1(A_430, B_431, A_7)=k1_relat_1(A_7) | ~r1_tarski(A_7, k2_zfmisc_1(A_430, B_431)))), inference(resolution, [status(thm)], [c_22, c_4401])).
% 8.77/3.03  tff(c_6588, plain, (![A_585]: (k1_relset_1(A_585, '#skF_4', '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_2', A_585))), inference(resolution, [status(thm)], [c_6585, c_4415])).
% 8.77/3.03  tff(c_6647, plain, (![A_587]: (k1_relset_1(A_587, '#skF_4', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_587))), inference(demodulation, [status(thm), theory('equality')], [c_4973, c_6588])).
% 8.77/3.03  tff(c_6652, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_10, c_6647])).
% 8.77/3.03  tff(c_50, plain, (![A_33]: (r2_hidden('#skF_1'(A_33), A_33) | k1_xboole_0=A_33)), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.77/3.03  tff(c_4138, plain, (![C_384, B_385, A_386]: (~v1_xboole_0(C_384) | ~m1_subset_1(B_385, k1_zfmisc_1(C_384)) | ~r2_hidden(A_386, B_385))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.77/3.03  tff(c_4188, plain, (![B_389, A_390, A_391]: (~v1_xboole_0(B_389) | ~r2_hidden(A_390, A_391) | ~r1_tarski(A_391, B_389))), inference(resolution, [status(thm)], [c_22, c_4138])).
% 8.77/3.03  tff(c_4192, plain, (![B_392, A_393]: (~v1_xboole_0(B_392) | ~r1_tarski(A_393, B_392) | k1_xboole_0=A_393)), inference(resolution, [status(thm)], [c_50, c_4188])).
% 8.77/3.03  tff(c_4210, plain, (~v1_xboole_0('#skF_4') | k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_4192])).
% 8.77/3.03  tff(c_4214, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_4210])).
% 8.77/3.03  tff(c_6583, plain, (![A_583]: (r1_tarski('#skF_5', k2_zfmisc_1(A_583, '#skF_4')) | ~r1_tarski('#skF_2', A_583))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_4973, c_6575])).
% 8.77/3.03  tff(c_7212, plain, (![B_611, A_612, A_613]: (k1_xboole_0=B_611 | k1_relset_1(A_612, B_611, A_613)=A_612 | ~v1_funct_2(A_613, A_612, B_611) | ~r1_tarski(A_613, k2_zfmisc_1(A_612, B_611)))), inference(resolution, [status(thm)], [c_22, c_4948])).
% 8.77/3.03  tff(c_7240, plain, (![A_583]: (k1_xboole_0='#skF_4' | k1_relset_1(A_583, '#skF_4', '#skF_5')=A_583 | ~v1_funct_2('#skF_5', A_583, '#skF_4') | ~r1_tarski('#skF_2', A_583))), inference(resolution, [status(thm)], [c_6583, c_7212])).
% 8.77/3.03  tff(c_7320, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_7240])).
% 8.77/3.03  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.77/3.03  tff(c_7409, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7320, c_2])).
% 8.77/3.03  tff(c_7412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4214, c_7409])).
% 8.77/3.03  tff(c_7414, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_7240])).
% 8.77/3.03  tff(c_4767, plain, (![B_467, C_468, A_469]: (k1_xboole_0=B_467 | v1_funct_2(C_468, A_469, B_467) | k1_relset_1(A_469, B_467, C_468)!=A_469 | ~m1_subset_1(C_468, k1_zfmisc_1(k2_zfmisc_1(A_469, B_467))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.77/3.03  tff(c_6879, plain, (![B_594, A_595, A_596]: (k1_xboole_0=B_594 | v1_funct_2(A_595, A_596, B_594) | k1_relset_1(A_596, B_594, A_595)!=A_596 | ~r1_tarski(A_595, k2_zfmisc_1(A_596, B_594)))), inference(resolution, [status(thm)], [c_22, c_4767])).
% 8.77/3.03  tff(c_6907, plain, (![A_583]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', A_583, '#skF_4') | k1_relset_1(A_583, '#skF_4', '#skF_5')!=A_583 | ~r1_tarski('#skF_2', A_583))), inference(resolution, [status(thm)], [c_6583, c_6879])).
% 8.77/3.03  tff(c_7666, plain, (![A_629]: (v1_funct_2('#skF_5', A_629, '#skF_4') | k1_relset_1(A_629, '#skF_4', '#skF_5')!=A_629 | ~r1_tarski('#skF_2', A_629))), inference(negUnitSimplification, [status(thm)], [c_7414, c_6907])).
% 8.77/3.03  tff(c_7672, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_7666, c_147])).
% 8.77/3.03  tff(c_7677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_6652, c_7672])).
% 8.77/3.03  tff(c_7679, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_4210])).
% 8.77/3.03  tff(c_123, plain, (![A_57]: (v1_xboole_0(k1_relat_1(A_57)) | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.77/3.03  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 8.77/3.03  tff(c_127, plain, (![A_57]: (k1_relat_1(A_57)=k1_xboole_0 | ~v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_123, c_4])).
% 8.77/3.03  tff(c_7682, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_7679, c_127])).
% 8.77/3.03  tff(c_7689, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3918, c_7682])).
% 8.77/3.03  tff(c_7690, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_3908])).
% 8.77/3.03  tff(c_36, plain, (![A_20]: (k2_relat_1(A_20)!=k1_xboole_0 | k1_xboole_0=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.77/3.03  tff(c_234, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_227, c_36])).
% 8.77/3.03  tff(c_236, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_234])).
% 8.77/3.03  tff(c_7695, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7690, c_236])).
% 8.77/3.03  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.77/3.03  tff(c_7708, plain, (![A_4]: (r1_tarski('#skF_4', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_7690, c_12])).
% 8.77/3.03  tff(c_258, plain, (![B_73, A_74]: (B_73=A_74 | ~r1_tarski(B_73, A_74) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.77/3.03  tff(c_268, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_72, c_258])).
% 8.77/3.03  tff(c_7746, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7708, c_268])).
% 8.77/3.03  tff(c_8237, plain, (![A_707, B_708, C_709]: (k2_relset_1(A_707, B_708, C_709)=k2_relat_1(C_709) | ~m1_subset_1(C_709, k1_zfmisc_1(k2_zfmisc_1(A_707, B_708))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.77/3.03  tff(c_8250, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_8237])).
% 8.77/3.03  tff(c_8253, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7746, c_8250])).
% 8.77/3.03  tff(c_8255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7695, c_8253])).
% 8.77/3.03  tff(c_8256, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_234])).
% 8.77/3.03  tff(c_8267, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8256, c_101])).
% 8.77/3.03  tff(c_129, plain, (![A_59]: (k1_relat_1(A_59)=k1_xboole_0 | ~v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_123, c_4])).
% 8.77/3.03  tff(c_137, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_129])).
% 8.77/3.03  tff(c_8262, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8256, c_8256, c_137])).
% 8.77/3.03  tff(c_8713, plain, (![A_776, B_777, C_778]: (k1_relset_1(A_776, B_777, C_778)=k1_relat_1(C_778) | ~m1_subset_1(C_778, k1_zfmisc_1(k2_zfmisc_1(A_776, B_777))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.77/3.03  tff(c_8726, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_8713])).
% 8.77/3.03  tff(c_8729, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8262, c_8726])).
% 8.77/3.03  tff(c_66, plain, (![B_48, A_47, C_49]: (k1_xboole_0=B_48 | k1_relset_1(A_47, B_48, C_49)=A_47 | ~v1_funct_2(C_49, A_47, B_48) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.77/3.03  tff(c_9177, plain, (![B_836, A_837, C_838]: (B_836='#skF_5' | k1_relset_1(A_837, B_836, C_838)=A_837 | ~v1_funct_2(C_838, A_837, B_836) | ~m1_subset_1(C_838, k1_zfmisc_1(k2_zfmisc_1(A_837, B_836))))), inference(demodulation, [status(thm), theory('equality')], [c_8256, c_66])).
% 8.77/3.03  tff(c_9193, plain, ('#skF_5'='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_9177])).
% 8.77/3.03  tff(c_9199, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_8729, c_9193])).
% 8.77/3.03  tff(c_9200, plain, ('#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_8267, c_9199])).
% 8.77/3.03  tff(c_8271, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8256, c_2])).
% 8.77/3.03  tff(c_9255, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9200, c_8271])).
% 8.77/3.03  tff(c_8266, plain, (![B_6]: (k2_zfmisc_1('#skF_5', B_6)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8256, c_8256, c_18])).
% 8.77/3.03  tff(c_9251, plain, (![B_6]: (k2_zfmisc_1('#skF_2', B_6)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9200, c_9200, c_8266])).
% 8.77/3.03  tff(c_8370, plain, (![C_718, B_719, A_720]: (~v1_xboole_0(C_718) | ~m1_subset_1(B_719, k1_zfmisc_1(C_718)) | ~r2_hidden(A_720, B_719))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.77/3.03  tff(c_8376, plain, (![A_720]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_720, '#skF_5'))), inference(resolution, [status(thm)], [c_74, c_8370])).
% 8.77/3.03  tff(c_8404, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_8376])).
% 8.77/3.03  tff(c_9349, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9251, c_8404])).
% 8.77/3.03  tff(c_9352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9255, c_9349])).
% 8.77/3.03  tff(c_9354, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_8376])).
% 8.77/3.03  tff(c_8269, plain, (![A_1]: (A_1='#skF_5' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_8256, c_4])).
% 8.77/3.03  tff(c_9385, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_9354, c_8269])).
% 8.77/3.03  tff(c_14, plain, (![B_6, A_5]: (k1_xboole_0=B_6 | k1_xboole_0=A_5 | k2_zfmisc_1(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.77/3.03  tff(c_9660, plain, (![B_893, A_894]: (B_893='#skF_5' | A_894='#skF_5' | k2_zfmisc_1(A_894, B_893)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8256, c_8256, c_8256, c_14])).
% 8.77/3.03  tff(c_9663, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_9385, c_9660])).
% 8.77/3.03  tff(c_9672, plain, ('#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_8267, c_9663])).
% 8.77/3.03  tff(c_9699, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9672, c_9672, c_8262])).
% 8.77/3.03  tff(c_8270, plain, (![A_4]: (r1_tarski('#skF_5', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_8256, c_12])).
% 8.77/3.03  tff(c_9701, plain, (![A_4]: (r1_tarski('#skF_2', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_9672, c_8270])).
% 8.77/3.03  tff(c_10154, plain, (![A_937, B_938, C_939]: (k1_relset_1(A_937, B_938, C_939)=k1_relat_1(C_939) | ~m1_subset_1(C_939, k1_zfmisc_1(k2_zfmisc_1(A_937, B_938))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.77/3.03  tff(c_10741, plain, (![A_997, B_998, A_999]: (k1_relset_1(A_997, B_998, A_999)=k1_relat_1(A_999) | ~r1_tarski(A_999, k2_zfmisc_1(A_997, B_998)))), inference(resolution, [status(thm)], [c_22, c_10154])).
% 8.77/3.03  tff(c_10754, plain, (![A_997, B_998]: (k1_relset_1(A_997, B_998, '#skF_2')=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_9701, c_10741])).
% 8.77/3.03  tff(c_10764, plain, (![A_997, B_998]: (k1_relset_1(A_997, B_998, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9699, c_10754])).
% 8.77/3.03  tff(c_9704, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9672, c_8256])).
% 8.77/3.03  tff(c_16, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.77/3.03  tff(c_56, plain, (![A_47]: (v1_funct_2(k1_xboole_0, A_47, k1_xboole_0) | k1_xboole_0=A_47 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_47, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.77/3.03  tff(c_84, plain, (![A_47]: (v1_funct_2(k1_xboole_0, A_47, k1_xboole_0) | k1_xboole_0=A_47 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_56])).
% 8.77/3.03  tff(c_9714, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_84])).
% 8.77/3.03  tff(c_9726, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_9704, c_9704, c_9714])).
% 8.77/3.03  tff(c_9729, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_9726])).
% 8.77/3.03  tff(c_9733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_9729])).
% 8.77/3.03  tff(c_9735, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_84])).
% 8.77/3.03  tff(c_9747, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_9704, c_9704, c_9735])).
% 8.77/3.03  tff(c_60, plain, (![C_49, B_48]: (v1_funct_2(C_49, k1_xboole_0, B_48) | k1_relset_1(k1_xboole_0, B_48, C_49)!=k1_xboole_0 | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_48))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.77/3.03  tff(c_82, plain, (![C_49, B_48]: (v1_funct_2(C_49, k1_xboole_0, B_48) | k1_relset_1(k1_xboole_0, B_48, C_49)!=k1_xboole_0 | ~m1_subset_1(C_49, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_60])).
% 8.77/3.03  tff(c_10250, plain, (![C_954, B_955]: (v1_funct_2(C_954, '#skF_2', B_955) | k1_relset_1('#skF_2', B_955, C_954)!='#skF_2' | ~m1_subset_1(C_954, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_9704, c_9704, c_9704, c_9704, c_82])).
% 8.77/3.03  tff(c_10276, plain, (![B_959]: (v1_funct_2('#skF_2', '#skF_2', B_959) | k1_relset_1('#skF_2', B_959, '#skF_2')!='#skF_2')), inference(resolution, [status(thm)], [c_9747, c_10250])).
% 8.77/3.03  tff(c_9706, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9672, c_147])).
% 8.77/3.03  tff(c_10287, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_2')!='#skF_2'), inference(resolution, [status(thm)], [c_10276, c_9706])).
% 8.77/3.03  tff(c_10772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10764, c_10287])).
% 8.77/3.03  tff(c_10773, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_80])).
% 8.77/3.03  tff(c_11408, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_11385, c_10773])).
% 8.77/3.03  tff(c_11426, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10847, c_11329, c_11408])).
% 8.77/3.03  tff(c_11429, plain, (~v4_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_11426])).
% 8.77/3.03  tff(c_11433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10847, c_11090, c_11429])).
% 8.77/3.03  tff(c_11435, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_70])).
% 8.77/3.03  tff(c_11434, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_70])).
% 8.77/3.03  tff(c_11444, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11435, c_11434])).
% 8.77/3.03  tff(c_11439, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11434, c_2])).
% 8.77/3.03  tff(c_11449, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11444, c_11439])).
% 8.77/3.03  tff(c_11495, plain, (![A_1108]: (v1_xboole_0(k1_relat_1(A_1108)) | ~v1_xboole_0(A_1108))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.77/3.03  tff(c_11437, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_11434, c_4])).
% 8.77/3.03  tff(c_11458, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_11444, c_11437])).
% 8.77/3.03  tff(c_11501, plain, (![A_1109]: (k1_relat_1(A_1109)='#skF_3' | ~v1_xboole_0(A_1109))), inference(resolution, [status(thm)], [c_11495, c_11458])).
% 8.77/3.03  tff(c_11509, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_11449, c_11501])).
% 8.77/3.03  tff(c_11438, plain, (![A_4]: (r1_tarski('#skF_2', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_11434, c_12])).
% 8.77/3.03  tff(c_11455, plain, (![A_4]: (r1_tarski('#skF_3', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_11444, c_11438])).
% 8.77/3.03  tff(c_12324, plain, (![A_1222, B_1223, C_1224]: (k1_relset_1(A_1222, B_1223, C_1224)=k1_relat_1(C_1224) | ~m1_subset_1(C_1224, k1_zfmisc_1(k2_zfmisc_1(A_1222, B_1223))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.77/3.03  tff(c_12526, plain, (![A_1247, B_1248, A_1249]: (k1_relset_1(A_1247, B_1248, A_1249)=k1_relat_1(A_1249) | ~r1_tarski(A_1249, k2_zfmisc_1(A_1247, B_1248)))), inference(resolution, [status(thm)], [c_22, c_12324])).
% 8.77/3.03  tff(c_12543, plain, (![A_1247, B_1248]: (k1_relset_1(A_1247, B_1248, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_11455, c_12526])).
% 8.77/3.03  tff(c_12550, plain, (![A_1247, B_1248]: (k1_relset_1(A_1247, B_1248, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11509, c_12543])).
% 8.77/3.03  tff(c_11466, plain, (![B_6]: (k2_zfmisc_1('#skF_3', B_6)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11435, c_11435, c_18])).
% 8.77/3.03  tff(c_11500, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11466, c_11444, c_74])).
% 8.77/3.03  tff(c_11574, plain, (![A_1116, B_1117]: (r1_tarski(A_1116, B_1117) | ~m1_subset_1(A_1116, k1_zfmisc_1(B_1117)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.77/3.03  tff(c_11582, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_11500, c_11574])).
% 8.77/3.03  tff(c_6, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.77/3.03  tff(c_11597, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_11582, c_6])).
% 8.77/3.03  tff(c_11600, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11455, c_11597])).
% 8.77/3.03  tff(c_11603, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11600, c_11500])).
% 8.77/3.03  tff(c_12935, plain, (![C_1277, B_1278]: (v1_funct_2(C_1277, '#skF_3', B_1278) | k1_relset_1('#skF_3', B_1278, C_1277)!='#skF_3' | ~m1_subset_1(C_1277, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_11435, c_11435, c_11435, c_11435, c_82])).
% 8.77/3.03  tff(c_12937, plain, (![B_1278]: (v1_funct_2('#skF_3', '#skF_3', B_1278) | k1_relset_1('#skF_3', B_1278, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_11603, c_12935])).
% 8.77/3.03  tff(c_12943, plain, (![B_1278]: (v1_funct_2('#skF_3', '#skF_3', B_1278))), inference(demodulation, [status(thm), theory('equality')], [c_12550, c_12937])).
% 8.77/3.03  tff(c_11522, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11444, c_11500, c_11466, c_11444, c_80])).
% 8.77/3.03  tff(c_11602, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11600, c_11522])).
% 8.77/3.03  tff(c_12948, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12943, c_11602])).
% 8.77/3.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.77/3.03  
% 8.77/3.03  Inference rules
% 8.77/3.03  ----------------------
% 8.77/3.03  #Ref     : 0
% 8.77/3.03  #Sup     : 2713
% 8.77/3.03  #Fact    : 0
% 8.77/3.03  #Define  : 0
% 8.77/3.03  #Split   : 62
% 8.77/3.03  #Chain   : 0
% 8.77/3.03  #Close   : 0
% 8.77/3.03  
% 8.77/3.03  Ordering : KBO
% 8.77/3.03  
% 8.77/3.03  Simplification rules
% 8.77/3.03  ----------------------
% 8.77/3.03  #Subsume      : 727
% 8.77/3.03  #Demod        : 2816
% 8.77/3.03  #Tautology    : 1302
% 8.77/3.03  #SimpNegUnit  : 106
% 8.77/3.03  #BackRed      : 374
% 8.77/3.03  
% 8.77/3.03  #Partial instantiations: 0
% 8.77/3.03  #Strategies tried      : 1
% 8.77/3.03  
% 8.77/3.03  Timing (in seconds)
% 8.77/3.03  ----------------------
% 8.77/3.03  Preprocessing        : 0.34
% 8.77/3.03  Parsing              : 0.18
% 8.77/3.03  CNF conversion       : 0.02
% 8.77/3.03  Main loop            : 1.88
% 8.77/3.03  Inferencing          : 0.60
% 8.77/3.03  Reduction            : 0.66
% 8.77/3.03  Demodulation         : 0.45
% 8.77/3.03  BG Simplification    : 0.06
% 8.77/3.03  Subsumption          : 0.40
% 8.77/3.03  Abstraction          : 0.07
% 8.77/3.03  MUC search           : 0.00
% 8.77/3.03  Cooper               : 0.00
% 8.77/3.03  Total                : 2.29
% 8.77/3.03  Index Insertion      : 0.00
% 8.77/3.03  Index Deletion       : 0.00
% 8.77/3.03  Index Matching       : 0.00
% 8.77/3.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
