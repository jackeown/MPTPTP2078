%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:19 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 197 expanded)
%              Number of leaves         :   33 (  85 expanded)
%              Depth                    :   12
%              Number of atoms          :  138 ( 525 expanded)
%              Number of equality atoms :   27 ( 100 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_43,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(c_45,plain,(
    ! [A_36] : k2_tarski(A_36,A_36) = k1_tarski(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7,B_8] : ~ v1_xboole_0(k2_tarski(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_50,plain,(
    ! [A_36] : ~ v1_xboole_0(k1_tarski(A_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_8])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_40,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_192,plain,(
    ! [D_97,C_98,B_99,A_100] :
      ( r2_hidden(k1_funct_1(D_97,C_98),B_99)
      | k1_xboole_0 = B_99
      | ~ r2_hidden(C_98,A_100)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99)))
      | ~ v1_funct_2(D_97,A_100,B_99)
      | ~ v1_funct_1(D_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_409,plain,(
    ! [D_121,A_122,B_123,B_124] :
      ( r2_hidden(k1_funct_1(D_121,A_122),B_123)
      | k1_xboole_0 = B_123
      | ~ m1_subset_1(D_121,k1_zfmisc_1(k2_zfmisc_1(B_124,B_123)))
      | ~ v1_funct_2(D_121,B_124,B_123)
      | ~ v1_funct_1(D_121)
      | v1_xboole_0(B_124)
      | ~ m1_subset_1(A_122,B_124) ) ),
    inference(resolution,[status(thm)],[c_20,c_192])).

tff(c_411,plain,(
    ! [A_122] :
      ( r2_hidden(k1_funct_1('#skF_4',A_122),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(k1_tarski('#skF_2'))
      | ~ m1_subset_1(A_122,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_38,c_409])).

tff(c_417,plain,(
    ! [A_122] :
      ( r2_hidden(k1_funct_1('#skF_4',A_122),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | v1_xboole_0(k1_tarski('#skF_2'))
      | ~ m1_subset_1(A_122,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_411])).

tff(c_420,plain,(
    ! [A_125] :
      ( r2_hidden(k1_funct_1('#skF_4',A_125),'#skF_3')
      | ~ m1_subset_1(A_125,k1_tarski('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_36,c_417])).

tff(c_34,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_433,plain,(
    ~ m1_subset_1('#skF_2',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_420,c_34])).

tff(c_16,plain,(
    ! [A_13] : m1_subset_1('#skF_1'(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_66,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_74,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_66])).

tff(c_28,plain,(
    ! [A_21,B_24] :
      ( k1_funct_1(A_21,B_24) = k1_xboole_0
      | r2_hidden(B_24,k1_relat_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_132,plain,(
    ! [B_69,A_70] :
      ( r2_hidden(k4_tarski(B_69,k1_funct_1(A_70,B_69)),A_70)
      | ~ r2_hidden(B_69,k1_relat_1(A_70))
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    ! [C_18,A_15,B_16] :
      ( r2_hidden(C_18,A_15)
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_296,plain,(
    ! [B_112,A_113,A_114] :
      ( r2_hidden(k4_tarski(B_112,k1_funct_1(A_113,B_112)),A_114)
      | ~ m1_subset_1(A_113,k1_zfmisc_1(A_114))
      | ~ r2_hidden(B_112,k1_relat_1(A_113))
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(resolution,[status(thm)],[c_132,c_18])).

tff(c_14,plain,(
    ! [C_11,A_9,B_10,D_12] :
      ( C_11 = A_9
      | ~ r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(k1_tarski(C_11),D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_326,plain,(
    ! [C_115,B_116,A_117,D_118] :
      ( C_115 = B_116
      | ~ m1_subset_1(A_117,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_115),D_118)))
      | ~ r2_hidden(B_116,k1_relat_1(A_117))
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(resolution,[status(thm)],[c_296,c_14])).

tff(c_328,plain,(
    ! [B_116] :
      ( B_116 = '#skF_2'
      | ~ r2_hidden(B_116,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_326])).

tff(c_338,plain,(
    ! [B_119] :
      ( B_119 = '#skF_2'
      | ~ r2_hidden(B_119,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_42,c_328])).

tff(c_366,plain,(
    ! [B_24] :
      ( B_24 = '#skF_2'
      | k1_funct_1('#skF_4',B_24) = k1_xboole_0
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_338])).

tff(c_379,plain,(
    ! [B_24] :
      ( B_24 = '#skF_2'
      | k1_funct_1('#skF_4',B_24) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_42,c_366])).

tff(c_430,plain,(
    ! [B_24] :
      ( r2_hidden(k1_xboole_0,'#skF_3')
      | ~ m1_subset_1(B_24,k1_tarski('#skF_2'))
      | B_24 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_420])).

tff(c_435,plain,(
    r2_hidden(k1_xboole_0,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_430])).

tff(c_12,plain,(
    ! [B_10,D_12,A_9,C_11] :
      ( r2_hidden(B_10,D_12)
      | ~ r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(k1_tarski(C_11),D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_740,plain,(
    ! [A_167,B_168,D_169,C_170] :
      ( r2_hidden(k1_funct_1(A_167,B_168),D_169)
      | ~ m1_subset_1(A_167,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_170),D_169)))
      | ~ r2_hidden(B_168,k1_relat_1(A_167))
      | ~ v1_funct_1(A_167)
      | ~ v1_relat_1(A_167) ) ),
    inference(resolution,[status(thm)],[c_296,c_12])).

tff(c_742,plain,(
    ! [B_168] :
      ( r2_hidden(k1_funct_1('#skF_4',B_168),'#skF_3')
      | ~ r2_hidden(B_168,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_740])).

tff(c_752,plain,(
    ! [B_171] :
      ( r2_hidden(k1_funct_1('#skF_4',B_171),'#skF_3')
      | ~ r2_hidden(B_171,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_42,c_742])).

tff(c_765,plain,(
    ~ r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_752,c_34])).

tff(c_774,plain,
    ( k1_funct_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_765])).

tff(c_780,plain,(
    k1_funct_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_42,c_774])).

tff(c_784,plain,(
    ~ r2_hidden(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_34])).

tff(c_787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_784])).

tff(c_823,plain,(
    ! [B_178] :
      ( ~ m1_subset_1(B_178,k1_tarski('#skF_2'))
      | B_178 = '#skF_2' ) ),
    inference(splitRight,[status(thm)],[c_430])).

tff(c_828,plain,(
    '#skF_1'(k1_tarski('#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_16,c_823])).

tff(c_832,plain,(
    m1_subset_1('#skF_2',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_828,c_16])).

tff(c_836,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_433,c_832])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.55  
% 3.36/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.55  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.36/1.55  
% 3.36/1.55  %Foreground sorts:
% 3.36/1.55  
% 3.36/1.55  
% 3.36/1.55  %Background operators:
% 3.36/1.55  
% 3.36/1.55  
% 3.36/1.55  %Foreground operators:
% 3.36/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.36/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.36/1.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.36/1.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.36/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.36/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.36/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.36/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.36/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.36/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.36/1.55  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.36/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.36/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.36/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.36/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.36/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.36/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.36/1.55  
% 3.48/1.57  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.48/1.57  tff(f_34, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_xboole_0)).
% 3.48/1.57  tff(f_102, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 3.48/1.57  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.48/1.57  tff(f_90, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.48/1.57  tff(f_43, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.48/1.57  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.48/1.57  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 3.48/1.57  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.48/1.57  tff(f_40, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 3.48/1.57  tff(c_45, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.48/1.57  tff(c_8, plain, (![A_7, B_8]: (~v1_xboole_0(k2_tarski(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.48/1.57  tff(c_50, plain, (![A_36]: (~v1_xboole_0(k1_tarski(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_45, c_8])).
% 3.48/1.57  tff(c_36, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.48/1.57  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.48/1.57  tff(c_40, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.48/1.57  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.48/1.57  tff(c_20, plain, (![A_19, B_20]: (r2_hidden(A_19, B_20) | v1_xboole_0(B_20) | ~m1_subset_1(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.48/1.57  tff(c_192, plain, (![D_97, C_98, B_99, A_100]: (r2_hidden(k1_funct_1(D_97, C_98), B_99) | k1_xboole_0=B_99 | ~r2_hidden(C_98, A_100) | ~m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))) | ~v1_funct_2(D_97, A_100, B_99) | ~v1_funct_1(D_97))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.48/1.57  tff(c_409, plain, (![D_121, A_122, B_123, B_124]: (r2_hidden(k1_funct_1(D_121, A_122), B_123) | k1_xboole_0=B_123 | ~m1_subset_1(D_121, k1_zfmisc_1(k2_zfmisc_1(B_124, B_123))) | ~v1_funct_2(D_121, B_124, B_123) | ~v1_funct_1(D_121) | v1_xboole_0(B_124) | ~m1_subset_1(A_122, B_124))), inference(resolution, [status(thm)], [c_20, c_192])).
% 3.48/1.57  tff(c_411, plain, (![A_122]: (r2_hidden(k1_funct_1('#skF_4', A_122), '#skF_3') | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0(k1_tarski('#skF_2')) | ~m1_subset_1(A_122, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_38, c_409])).
% 3.48/1.57  tff(c_417, plain, (![A_122]: (r2_hidden(k1_funct_1('#skF_4', A_122), '#skF_3') | k1_xboole_0='#skF_3' | v1_xboole_0(k1_tarski('#skF_2')) | ~m1_subset_1(A_122, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_411])).
% 3.48/1.57  tff(c_420, plain, (![A_125]: (r2_hidden(k1_funct_1('#skF_4', A_125), '#skF_3') | ~m1_subset_1(A_125, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_36, c_417])).
% 3.48/1.57  tff(c_34, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.48/1.57  tff(c_433, plain, (~m1_subset_1('#skF_2', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_420, c_34])).
% 3.48/1.57  tff(c_16, plain, (![A_13]: (m1_subset_1('#skF_1'(A_13), A_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.48/1.57  tff(c_66, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.48/1.57  tff(c_74, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_66])).
% 3.48/1.57  tff(c_28, plain, (![A_21, B_24]: (k1_funct_1(A_21, B_24)=k1_xboole_0 | r2_hidden(B_24, k1_relat_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.48/1.57  tff(c_132, plain, (![B_69, A_70]: (r2_hidden(k4_tarski(B_69, k1_funct_1(A_70, B_69)), A_70) | ~r2_hidden(B_69, k1_relat_1(A_70)) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.48/1.57  tff(c_18, plain, (![C_18, A_15, B_16]: (r2_hidden(C_18, A_15) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.48/1.57  tff(c_296, plain, (![B_112, A_113, A_114]: (r2_hidden(k4_tarski(B_112, k1_funct_1(A_113, B_112)), A_114) | ~m1_subset_1(A_113, k1_zfmisc_1(A_114)) | ~r2_hidden(B_112, k1_relat_1(A_113)) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(resolution, [status(thm)], [c_132, c_18])).
% 3.48/1.57  tff(c_14, plain, (![C_11, A_9, B_10, D_12]: (C_11=A_9 | ~r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(k1_tarski(C_11), D_12)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.48/1.57  tff(c_326, plain, (![C_115, B_116, A_117, D_118]: (C_115=B_116 | ~m1_subset_1(A_117, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_115), D_118))) | ~r2_hidden(B_116, k1_relat_1(A_117)) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117))), inference(resolution, [status(thm)], [c_296, c_14])).
% 3.48/1.57  tff(c_328, plain, (![B_116]: (B_116='#skF_2' | ~r2_hidden(B_116, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_326])).
% 3.48/1.57  tff(c_338, plain, (![B_119]: (B_119='#skF_2' | ~r2_hidden(B_119, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_42, c_328])).
% 3.48/1.57  tff(c_366, plain, (![B_24]: (B_24='#skF_2' | k1_funct_1('#skF_4', B_24)=k1_xboole_0 | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_338])).
% 3.48/1.57  tff(c_379, plain, (![B_24]: (B_24='#skF_2' | k1_funct_1('#skF_4', B_24)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_42, c_366])).
% 3.48/1.57  tff(c_430, plain, (![B_24]: (r2_hidden(k1_xboole_0, '#skF_3') | ~m1_subset_1(B_24, k1_tarski('#skF_2')) | B_24='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_379, c_420])).
% 3.48/1.57  tff(c_435, plain, (r2_hidden(k1_xboole_0, '#skF_3')), inference(splitLeft, [status(thm)], [c_430])).
% 3.48/1.57  tff(c_12, plain, (![B_10, D_12, A_9, C_11]: (r2_hidden(B_10, D_12) | ~r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(k1_tarski(C_11), D_12)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.48/1.57  tff(c_740, plain, (![A_167, B_168, D_169, C_170]: (r2_hidden(k1_funct_1(A_167, B_168), D_169) | ~m1_subset_1(A_167, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_170), D_169))) | ~r2_hidden(B_168, k1_relat_1(A_167)) | ~v1_funct_1(A_167) | ~v1_relat_1(A_167))), inference(resolution, [status(thm)], [c_296, c_12])).
% 3.48/1.57  tff(c_742, plain, (![B_168]: (r2_hidden(k1_funct_1('#skF_4', B_168), '#skF_3') | ~r2_hidden(B_168, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_740])).
% 3.48/1.57  tff(c_752, plain, (![B_171]: (r2_hidden(k1_funct_1('#skF_4', B_171), '#skF_3') | ~r2_hidden(B_171, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_42, c_742])).
% 3.48/1.57  tff(c_765, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_752, c_34])).
% 3.48/1.57  tff(c_774, plain, (k1_funct_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_765])).
% 3.48/1.57  tff(c_780, plain, (k1_funct_1('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_74, c_42, c_774])).
% 3.48/1.57  tff(c_784, plain, (~r2_hidden(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_780, c_34])).
% 3.48/1.57  tff(c_787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_435, c_784])).
% 3.48/1.57  tff(c_823, plain, (![B_178]: (~m1_subset_1(B_178, k1_tarski('#skF_2')) | B_178='#skF_2')), inference(splitRight, [status(thm)], [c_430])).
% 3.48/1.57  tff(c_828, plain, ('#skF_1'(k1_tarski('#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_16, c_823])).
% 3.48/1.57  tff(c_832, plain, (m1_subset_1('#skF_2', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_828, c_16])).
% 3.48/1.57  tff(c_836, plain, $false, inference(negUnitSimplification, [status(thm)], [c_433, c_832])).
% 3.48/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.57  
% 3.48/1.57  Inference rules
% 3.48/1.57  ----------------------
% 3.48/1.57  #Ref     : 0
% 3.48/1.57  #Sup     : 173
% 3.48/1.57  #Fact    : 0
% 3.48/1.57  #Define  : 0
% 3.48/1.57  #Split   : 12
% 3.48/1.57  #Chain   : 0
% 3.48/1.57  #Close   : 0
% 3.48/1.57  
% 3.48/1.57  Ordering : KBO
% 3.48/1.57  
% 3.48/1.57  Simplification rules
% 3.48/1.57  ----------------------
% 3.48/1.57  #Subsume      : 7
% 3.48/1.57  #Demod        : 24
% 3.48/1.57  #Tautology    : 15
% 3.48/1.57  #SimpNegUnit  : 2
% 3.48/1.57  #BackRed      : 2
% 3.48/1.57  
% 3.48/1.57  #Partial instantiations: 0
% 3.48/1.57  #Strategies tried      : 1
% 3.48/1.57  
% 3.48/1.57  Timing (in seconds)
% 3.48/1.57  ----------------------
% 3.48/1.57  Preprocessing        : 0.33
% 3.48/1.57  Parsing              : 0.18
% 3.48/1.57  CNF conversion       : 0.02
% 3.48/1.57  Main loop            : 0.44
% 3.48/1.57  Inferencing          : 0.15
% 3.48/1.57  Reduction            : 0.12
% 3.48/1.57  Demodulation         : 0.08
% 3.48/1.57  BG Simplification    : 0.02
% 3.48/1.57  Subsumption          : 0.10
% 3.48/1.57  Abstraction          : 0.03
% 3.48/1.57  MUC search           : 0.00
% 3.48/1.57  Cooper               : 0.00
% 3.48/1.57  Total                : 0.80
% 3.48/1.57  Index Insertion      : 0.00
% 3.48/1.57  Index Deletion       : 0.00
% 3.48/1.57  Index Matching       : 0.00
% 3.48/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
