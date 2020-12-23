%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:44 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 249 expanded)
%              Number of leaves         :   42 ( 102 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 394 expanded)
%              Number of equality atoms :   18 (  96 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_80,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_72,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_70,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_74,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_111,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_58,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_58,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_38,plain,(
    ! [A_33,B_34] : r1_xboole_0(k4_xboole_0(A_33,B_34),B_34) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_401,plain,(
    ! [A_102,B_103] :
      ( r2_hidden('#skF_1'(A_102,B_103),A_102)
      | r1_tarski(A_102,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_699,plain,(
    ! [A_132,B_133,B_134] :
      ( ~ r1_xboole_0(A_132,B_133)
      | r1_tarski(k3_xboole_0(A_132,B_133),B_134) ) ),
    inference(resolution,[status(thm)],[c_401,c_12])).

tff(c_30,plain,(
    ! [A_25] : r1_tarski(k1_xboole_0,A_25) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_307,plain,(
    ! [B_93,A_94] :
      ( B_93 = A_94
      | ~ r1_tarski(B_93,A_94)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_322,plain,(
    ! [A_25] :
      ( k1_xboole_0 = A_25
      | ~ r1_tarski(A_25,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_30,c_307])).

tff(c_777,plain,(
    ! [A_140,B_141] :
      ( k3_xboole_0(A_140,B_141) = k1_xboole_0
      | ~ r1_xboole_0(A_140,B_141) ) ),
    inference(resolution,[status(thm)],[c_699,c_322])).

tff(c_792,plain,(
    ! [A_142,B_143] : k3_xboole_0(k4_xboole_0(A_142,B_143),B_143) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_777])).

tff(c_34,plain,(
    ! [A_29,B_30] : r1_tarski(k4_xboole_0(A_29,B_30),A_29) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_113,plain,(
    ! [A_74,B_75] :
      ( k3_xboole_0(A_74,B_75) = A_74
      | ~ r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_126,plain,(
    ! [A_29,B_30] : k3_xboole_0(k4_xboole_0(A_29,B_30),A_29) = k4_xboole_0(A_29,B_30) ),
    inference(resolution,[status(thm)],[c_34,c_113])).

tff(c_804,plain,(
    ! [B_143] : k4_xboole_0(B_143,B_143) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_792,c_126])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_420,plain,(
    ! [A_106,B_107] : k2_xboole_0(k3_xboole_0(A_106,B_107),k4_xboole_0(A_106,B_107)) = A_106 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_435,plain,(
    ! [A_6] : k2_xboole_0(A_6,k4_xboole_0(A_6,A_6)) = A_6 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_420])).

tff(c_1437,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_435])).

tff(c_28,plain,(
    ! [A_24] : k3_xboole_0(A_24,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1571,plain,(
    ! [A_172,B_173,C_174] : r1_tarski(k2_xboole_0(k3_xboole_0(A_172,B_173),k3_xboole_0(A_172,C_174)),k2_xboole_0(B_173,C_174)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1624,plain,(
    ! [A_24,B_173] : r1_tarski(k2_xboole_0(k3_xboole_0(A_24,B_173),k1_xboole_0),k2_xboole_0(B_173,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1571])).

tff(c_1634,plain,(
    ! [A_175,B_176] : r1_tarski(k3_xboole_0(A_175,B_176),B_176) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_1437,c_1624])).

tff(c_50,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(A_44,k1_zfmisc_1(B_45))
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_183,plain,(
    ! [B_83,A_84] :
      ( v1_relat_1(B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_84))
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_187,plain,(
    ! [A_44,B_45] :
      ( v1_relat_1(A_44)
      | ~ v1_relat_1(B_45)
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_50,c_183])).

tff(c_1665,plain,(
    ! [A_175,B_176] :
      ( v1_relat_1(k3_xboole_0(A_175,B_176))
      | ~ v1_relat_1(B_176) ) ),
    inference(resolution,[status(thm)],[c_1634,c_187])).

tff(c_62,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1633,plain,(
    ! [A_24,B_173] : r1_tarski(k3_xboole_0(A_24,B_173),B_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_1437,c_1624])).

tff(c_2004,plain,(
    ! [C_187,A_188,B_189] :
      ( r1_tarski(k5_relat_1(C_187,A_188),k5_relat_1(C_187,B_189))
      | ~ r1_tarski(A_188,B_189)
      | ~ v1_relat_1(C_187)
      | ~ v1_relat_1(B_189)
      | ~ v1_relat_1(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_856,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_435])).

tff(c_932,plain,(
    ! [A_147,B_148,C_149] : r1_tarski(k2_xboole_0(k3_xboole_0(A_147,B_148),k3_xboole_0(A_147,C_149)),k2_xboole_0(B_148,C_149)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_985,plain,(
    ! [A_24,B_148] : r1_tarski(k2_xboole_0(k3_xboole_0(A_24,B_148),k1_xboole_0),k2_xboole_0(B_148,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_932])).

tff(c_995,plain,(
    ! [A_150,B_151] : r1_tarski(k3_xboole_0(A_150,B_151),B_151) ),
    inference(demodulation,[status(thm),theory(equality)],[c_856,c_856,c_985])).

tff(c_1026,plain,(
    ! [A_150,B_151] :
      ( v1_relat_1(k3_xboole_0(A_150,B_151))
      | ~ v1_relat_1(B_151) ) ),
    inference(resolution,[status(thm)],[c_995,c_187])).

tff(c_60,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_22,plain,(
    ! [A_17,B_18] : r1_tarski(k3_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1407,plain,(
    ! [C_164,A_165,B_166] :
      ( r1_tarski(k5_relat_1(C_164,A_165),k5_relat_1(C_164,B_166))
      | ~ r1_tarski(A_165,B_166)
      | ~ v1_relat_1(C_164)
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_735,plain,(
    ! [A_135,B_136,C_137] :
      ( r1_tarski(A_135,k3_xboole_0(B_136,C_137))
      | ~ r1_tarski(A_135,C_137)
      | ~ r1_tarski(A_135,B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_56,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k3_xboole_0(k5_relat_1('#skF_3','#skF_4'),k5_relat_1('#skF_3','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_765,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_735,c_56])).

tff(c_855,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_765])).

tff(c_1410,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1407,c_855])).

tff(c_1421,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_22,c_1410])).

tff(c_1427,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1026,c_1421])).

tff(c_1434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1427])).

tff(c_1435,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_765])).

tff(c_2007,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_2004,c_1435])).

tff(c_2018,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_1633,c_2007])).

tff(c_2024,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1665,c_2018])).

tff(c_2031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2024])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:27:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.57  
% 3.38/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.58  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.38/1.58  
% 3.38/1.58  %Foreground sorts:
% 3.38/1.58  
% 3.38/1.58  
% 3.38/1.58  %Background operators:
% 3.38/1.58  
% 3.38/1.58  
% 3.38/1.58  %Foreground operators:
% 3.38/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.38/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.58  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.38/1.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.38/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.38/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.38/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.38/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.38/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.38/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.38/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.38/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.38/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.38/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.38/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.38/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.38/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.38/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.38/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.38/1.58  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.38/1.58  
% 3.38/1.59  tff(f_122, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 3.38/1.59  tff(f_80, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.38/1.59  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.38/1.59  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.38/1.59  tff(f_72, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.38/1.59  tff(f_54, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.38/1.59  tff(f_76, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.38/1.59  tff(f_68, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.38/1.59  tff(f_34, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.38/1.59  tff(f_78, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.38/1.59  tff(f_70, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.38/1.59  tff(f_74, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 3.38/1.59  tff(f_92, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.38/1.59  tff(f_99, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.38/1.59  tff(f_111, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 3.38/1.59  tff(f_58, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.38/1.59  tff(f_64, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.38/1.59  tff(c_58, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.38/1.59  tff(c_38, plain, (![A_33, B_34]: (r1_xboole_0(k4_xboole_0(A_33, B_34), B_34))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.38/1.59  tff(c_401, plain, (![A_102, B_103]: (r2_hidden('#skF_1'(A_102, B_103), A_102) | r1_tarski(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.38/1.59  tff(c_12, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.38/1.59  tff(c_699, plain, (![A_132, B_133, B_134]: (~r1_xboole_0(A_132, B_133) | r1_tarski(k3_xboole_0(A_132, B_133), B_134))), inference(resolution, [status(thm)], [c_401, c_12])).
% 3.38/1.59  tff(c_30, plain, (![A_25]: (r1_tarski(k1_xboole_0, A_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.38/1.59  tff(c_307, plain, (![B_93, A_94]: (B_93=A_94 | ~r1_tarski(B_93, A_94) | ~r1_tarski(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.38/1.59  tff(c_322, plain, (![A_25]: (k1_xboole_0=A_25 | ~r1_tarski(A_25, k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_307])).
% 3.38/1.59  tff(c_777, plain, (![A_140, B_141]: (k3_xboole_0(A_140, B_141)=k1_xboole_0 | ~r1_xboole_0(A_140, B_141))), inference(resolution, [status(thm)], [c_699, c_322])).
% 3.38/1.59  tff(c_792, plain, (![A_142, B_143]: (k3_xboole_0(k4_xboole_0(A_142, B_143), B_143)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_777])).
% 3.38/1.59  tff(c_34, plain, (![A_29, B_30]: (r1_tarski(k4_xboole_0(A_29, B_30), A_29))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.38/1.59  tff(c_113, plain, (![A_74, B_75]: (k3_xboole_0(A_74, B_75)=A_74 | ~r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.38/1.59  tff(c_126, plain, (![A_29, B_30]: (k3_xboole_0(k4_xboole_0(A_29, B_30), A_29)=k4_xboole_0(A_29, B_30))), inference(resolution, [status(thm)], [c_34, c_113])).
% 3.38/1.59  tff(c_804, plain, (![B_143]: (k4_xboole_0(B_143, B_143)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_792, c_126])).
% 3.38/1.59  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.38/1.59  tff(c_420, plain, (![A_106, B_107]: (k2_xboole_0(k3_xboole_0(A_106, B_107), k4_xboole_0(A_106, B_107))=A_106)), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.38/1.59  tff(c_435, plain, (![A_6]: (k2_xboole_0(A_6, k4_xboole_0(A_6, A_6))=A_6)), inference(superposition, [status(thm), theory('equality')], [c_8, c_420])).
% 3.38/1.59  tff(c_1437, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_804, c_435])).
% 3.38/1.59  tff(c_28, plain, (![A_24]: (k3_xboole_0(A_24, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.38/1.59  tff(c_1571, plain, (![A_172, B_173, C_174]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_172, B_173), k3_xboole_0(A_172, C_174)), k2_xboole_0(B_173, C_174)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.38/1.59  tff(c_1624, plain, (![A_24, B_173]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_24, B_173), k1_xboole_0), k2_xboole_0(B_173, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1571])).
% 3.38/1.59  tff(c_1634, plain, (![A_175, B_176]: (r1_tarski(k3_xboole_0(A_175, B_176), B_176))), inference(demodulation, [status(thm), theory('equality')], [c_1437, c_1437, c_1624])).
% 3.38/1.59  tff(c_50, plain, (![A_44, B_45]: (m1_subset_1(A_44, k1_zfmisc_1(B_45)) | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.38/1.59  tff(c_183, plain, (![B_83, A_84]: (v1_relat_1(B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_84)) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.38/1.59  tff(c_187, plain, (![A_44, B_45]: (v1_relat_1(A_44) | ~v1_relat_1(B_45) | ~r1_tarski(A_44, B_45))), inference(resolution, [status(thm)], [c_50, c_183])).
% 3.38/1.59  tff(c_1665, plain, (![A_175, B_176]: (v1_relat_1(k3_xboole_0(A_175, B_176)) | ~v1_relat_1(B_176))), inference(resolution, [status(thm)], [c_1634, c_187])).
% 3.38/1.59  tff(c_62, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.38/1.59  tff(c_1633, plain, (![A_24, B_173]: (r1_tarski(k3_xboole_0(A_24, B_173), B_173))), inference(demodulation, [status(thm), theory('equality')], [c_1437, c_1437, c_1624])).
% 3.38/1.59  tff(c_2004, plain, (![C_187, A_188, B_189]: (r1_tarski(k5_relat_1(C_187, A_188), k5_relat_1(C_187, B_189)) | ~r1_tarski(A_188, B_189) | ~v1_relat_1(C_187) | ~v1_relat_1(B_189) | ~v1_relat_1(A_188))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.38/1.59  tff(c_856, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_804, c_435])).
% 3.38/1.59  tff(c_932, plain, (![A_147, B_148, C_149]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_147, B_148), k3_xboole_0(A_147, C_149)), k2_xboole_0(B_148, C_149)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.38/1.59  tff(c_985, plain, (![A_24, B_148]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_24, B_148), k1_xboole_0), k2_xboole_0(B_148, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_932])).
% 3.38/1.59  tff(c_995, plain, (![A_150, B_151]: (r1_tarski(k3_xboole_0(A_150, B_151), B_151))), inference(demodulation, [status(thm), theory('equality')], [c_856, c_856, c_985])).
% 3.38/1.59  tff(c_1026, plain, (![A_150, B_151]: (v1_relat_1(k3_xboole_0(A_150, B_151)) | ~v1_relat_1(B_151))), inference(resolution, [status(thm)], [c_995, c_187])).
% 3.38/1.59  tff(c_60, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.38/1.59  tff(c_22, plain, (![A_17, B_18]: (r1_tarski(k3_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.38/1.59  tff(c_1407, plain, (![C_164, A_165, B_166]: (r1_tarski(k5_relat_1(C_164, A_165), k5_relat_1(C_164, B_166)) | ~r1_tarski(A_165, B_166) | ~v1_relat_1(C_164) | ~v1_relat_1(B_166) | ~v1_relat_1(A_165))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.38/1.59  tff(c_735, plain, (![A_135, B_136, C_137]: (r1_tarski(A_135, k3_xboole_0(B_136, C_137)) | ~r1_tarski(A_135, C_137) | ~r1_tarski(A_135, B_136))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.38/1.59  tff(c_56, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k3_xboole_0(k5_relat_1('#skF_3', '#skF_4'), k5_relat_1('#skF_3', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.38/1.59  tff(c_765, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5')) | ~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_735, c_56])).
% 3.38/1.59  tff(c_855, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_765])).
% 3.38/1.59  tff(c_1410, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1407, c_855])).
% 3.38/1.59  tff(c_1421, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_22, c_1410])).
% 3.38/1.59  tff(c_1427, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1026, c_1421])).
% 3.38/1.59  tff(c_1434, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_1427])).
% 3.38/1.59  tff(c_1435, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_765])).
% 3.38/1.59  tff(c_2007, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_2004, c_1435])).
% 3.38/1.59  tff(c_2018, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_1633, c_2007])).
% 3.38/1.59  tff(c_2024, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1665, c_2018])).
% 3.38/1.59  tff(c_2031, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_2024])).
% 3.38/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.59  
% 3.38/1.59  Inference rules
% 3.38/1.59  ----------------------
% 3.38/1.59  #Ref     : 0
% 3.38/1.59  #Sup     : 485
% 3.38/1.59  #Fact    : 0
% 3.38/1.59  #Define  : 0
% 3.38/1.59  #Split   : 3
% 3.38/1.59  #Chain   : 0
% 3.38/1.59  #Close   : 0
% 3.38/1.59  
% 3.38/1.59  Ordering : KBO
% 3.38/1.59  
% 3.38/1.59  Simplification rules
% 3.38/1.59  ----------------------
% 3.38/1.59  #Subsume      : 27
% 3.38/1.59  #Demod        : 359
% 3.38/1.59  #Tautology    : 337
% 3.38/1.59  #SimpNegUnit  : 8
% 3.38/1.59  #BackRed      : 9
% 3.38/1.59  
% 3.38/1.59  #Partial instantiations: 0
% 3.38/1.59  #Strategies tried      : 1
% 3.38/1.59  
% 3.38/1.59  Timing (in seconds)
% 3.38/1.59  ----------------------
% 3.38/1.59  Preprocessing        : 0.32
% 3.38/1.59  Parsing              : 0.17
% 3.38/1.59  CNF conversion       : 0.02
% 3.38/1.60  Main loop            : 0.46
% 3.38/1.60  Inferencing          : 0.16
% 3.38/1.60  Reduction            : 0.17
% 3.38/1.60  Demodulation         : 0.12
% 3.38/1.60  BG Simplification    : 0.02
% 3.38/1.60  Subsumption          : 0.07
% 3.38/1.60  Abstraction          : 0.03
% 3.38/1.60  MUC search           : 0.00
% 3.38/1.60  Cooper               : 0.00
% 3.38/1.60  Total                : 0.81
% 3.38/1.60  Index Insertion      : 0.00
% 3.38/1.60  Index Deletion       : 0.00
% 3.38/1.60  Index Matching       : 0.00
% 3.38/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
