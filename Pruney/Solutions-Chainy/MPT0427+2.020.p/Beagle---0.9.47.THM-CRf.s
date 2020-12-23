%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:59 EST 2020

% Result     : Theorem 7.83s
% Output     : CNFRefutation 7.83s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 196 expanded)
%              Number of leaves         :   31 (  76 expanded)
%              Depth                    :    9
%              Number of atoms          :  152 ( 387 expanded)
%              Number of equality atoms :   42 ( 111 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_65,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_502,plain,(
    ! [A_92,B_93] :
      ( m1_subset_1(k8_setfam_1(A_92,B_93),k1_zfmisc_1(A_92))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k1_zfmisc_1(A_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_593,plain,(
    ! [A_104,B_105] :
      ( r1_tarski(k8_setfam_1(A_104,B_105),A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(k1_zfmisc_1(A_104))) ) ),
    inference(resolution,[status(thm)],[c_502,c_44])).

tff(c_617,plain,(
    r1_tarski(k8_setfam_1('#skF_4','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_593])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_280,plain,(
    ! [A_73,B_74] :
      ( k6_setfam_1(A_73,B_74) = k1_setfam_1(B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(A_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_302,plain,(
    k6_setfam_1('#skF_4','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_280])).

tff(c_760,plain,(
    ! [A_113,B_114] :
      ( k8_setfam_1(A_113,B_114) = k6_setfam_1(A_113,B_114)
      | k1_xboole_0 = B_114
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k1_zfmisc_1(A_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_782,plain,
    ( k8_setfam_1('#skF_4','#skF_5') = k6_setfam_1('#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_62,c_760])).

tff(c_795,plain,
    ( k8_setfam_1('#skF_4','#skF_5') = k1_setfam_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_782])).

tff(c_829,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_795])).

tff(c_34,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36,plain,(
    ! [A_17] :
      ( k8_setfam_1(A_17,k1_xboole_0) = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_64,plain,(
    ! [A_17] : k8_setfam_1(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36])).

tff(c_847,plain,(
    ! [A_17] : k8_setfam_1(A_17,'#skF_5') = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_829,c_64])).

tff(c_618,plain,(
    r1_tarski(k8_setfam_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_593])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_632,plain,
    ( k8_setfam_1('#skF_4','#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k8_setfam_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_618,c_2])).

tff(c_759,plain,(
    ~ r1_tarski('#skF_4',k8_setfam_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_632])).

tff(c_901,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_759])).

tff(c_906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_901])).

tff(c_908,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_795])).

tff(c_58,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_46,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12,plain,(
    ! [C_8,A_4] :
      ( r2_hidden(C_8,k1_zfmisc_1(A_4))
      | ~ r1_tarski(C_8,A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_182,plain,(
    ! [C_59,A_60,B_61] :
      ( r2_hidden(C_59,A_60)
      | ~ r2_hidden(C_59,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1467,plain,(
    ! [C_157,A_158,A_159] :
      ( r2_hidden(C_157,A_158)
      | ~ m1_subset_1(k1_zfmisc_1(A_159),k1_zfmisc_1(A_158))
      | ~ r1_tarski(C_157,A_159) ) ),
    inference(resolution,[status(thm)],[c_12,c_182])).

tff(c_1717,plain,(
    ! [C_173,B_174,A_175] :
      ( r2_hidden(C_173,B_174)
      | ~ r1_tarski(C_173,A_175)
      | ~ r1_tarski(k1_zfmisc_1(A_175),B_174) ) ),
    inference(resolution,[status(thm)],[c_46,c_1467])).

tff(c_1766,plain,(
    ! [B_176] :
      ( r2_hidden('#skF_5',B_176)
      | ~ r1_tarski(k1_zfmisc_1('#skF_6'),B_176) ) ),
    inference(resolution,[status(thm)],[c_58,c_1717])).

tff(c_1771,plain,(
    r2_hidden('#skF_5',k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6,c_1766])).

tff(c_517,plain,(
    ! [A_17] :
      ( m1_subset_1(A_17,k1_zfmisc_1(A_17))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_502])).

tff(c_524,plain,(
    ! [A_94] : m1_subset_1(A_94,k1_zfmisc_1(A_94)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_517])).

tff(c_48,plain,(
    ! [A_25,C_27,B_26] :
      ( m1_subset_1(A_25,C_27)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(C_27))
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_541,plain,(
    ! [A_25,A_94] :
      ( m1_subset_1(A_25,A_94)
      | ~ r2_hidden(A_25,A_94) ) ),
    inference(resolution,[status(thm)],[c_524,c_48])).

tff(c_1789,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1771,c_541])).

tff(c_420,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_3'(A_86,B_87),A_86)
      | r1_tarski(B_87,k1_setfam_1(A_86))
      | k1_xboole_0 = A_86 ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_32,plain,(
    ! [C_15,A_12,B_13] :
      ( r2_hidden(C_15,A_12)
      | ~ r2_hidden(C_15,B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_435,plain,(
    ! [A_86,B_87,A_12] :
      ( r2_hidden('#skF_3'(A_86,B_87),A_12)
      | ~ m1_subset_1(A_86,k1_zfmisc_1(A_12))
      | r1_tarski(B_87,k1_setfam_1(A_86))
      | k1_xboole_0 = A_86 ) ),
    inference(resolution,[status(thm)],[c_420,c_32])).

tff(c_190,plain,(
    ! [B_62,C_63,A_64] :
      ( r1_tarski(k1_setfam_1(B_62),C_63)
      | ~ r1_tarski(A_64,C_63)
      | ~ r2_hidden(A_64,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_203,plain,(
    ! [B_62,B_2] :
      ( r1_tarski(k1_setfam_1(B_62),B_2)
      | ~ r2_hidden(B_2,B_62) ) ),
    inference(resolution,[status(thm)],[c_6,c_190])).

tff(c_633,plain,(
    ! [B_106,A_107] :
      ( ~ r1_tarski(B_106,'#skF_3'(A_107,B_106))
      | r1_tarski(B_106,k1_setfam_1(A_107))
      | k1_xboole_0 = A_107 ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_7847,plain,(
    ! [B_354,A_355] :
      ( r1_tarski(k1_setfam_1(B_354),k1_setfam_1(A_355))
      | k1_xboole_0 = A_355
      | ~ r2_hidden('#skF_3'(A_355,k1_setfam_1(B_354)),B_354) ) ),
    inference(resolution,[status(thm)],[c_203,c_633])).

tff(c_8971,plain,(
    ! [A_381,A_382] :
      ( ~ m1_subset_1(A_381,k1_zfmisc_1(A_382))
      | r1_tarski(k1_setfam_1(A_382),k1_setfam_1(A_381))
      | k1_xboole_0 = A_381 ) ),
    inference(resolution,[status(thm)],[c_435,c_7847])).

tff(c_907,plain,(
    k8_setfam_1('#skF_4','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_795])).

tff(c_301,plain,(
    k6_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_280])).

tff(c_779,plain,
    ( k8_setfam_1('#skF_4','#skF_6') = k6_setfam_1('#skF_4','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_60,c_760])).

tff(c_793,plain,
    ( k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_779])).

tff(c_799,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_793])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_817,plain,(
    ! [A_3] : r1_tarski('#skF_6',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_8])).

tff(c_148,plain,(
    ! [B_56,A_57] :
      ( B_56 = A_57
      | ~ r1_tarski(B_56,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_166,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_148])).

tff(c_180,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_826,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_180])).

tff(c_827,plain,(
    k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_793])).

tff(c_56,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_4','#skF_6'),k8_setfam_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_923,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_6'),k8_setfam_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_827,c_56])).

tff(c_978,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_6'),k1_setfam_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_923])).

tff(c_8994,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_6'))
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8971,c_978])).

tff(c_9068,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1789,c_8994])).

tff(c_9070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_908,c_9068])).

tff(c_9071,plain,(
    k8_setfam_1('#skF_4','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_632])).

tff(c_9074,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_4','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9071,c_56])).

tff(c_9078,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_9074])).

tff(c_9079,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_9089,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_4','#skF_6'),k8_setfam_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9079,c_56])).

tff(c_9095,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9089])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.83/2.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.83/2.86  
% 7.83/2.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.83/2.87  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 7.83/2.87  
% 7.83/2.87  %Foreground sorts:
% 7.83/2.87  
% 7.83/2.87  
% 7.83/2.87  %Background operators:
% 7.83/2.87  
% 7.83/2.87  
% 7.83/2.87  %Foreground operators:
% 7.83/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.83/2.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.83/2.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.83/2.87  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 7.83/2.87  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.83/2.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.83/2.87  tff('#skF_5', type, '#skF_5': $i).
% 7.83/2.87  tff('#skF_6', type, '#skF_6': $i).
% 7.83/2.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.83/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.83/2.87  tff('#skF_4', type, '#skF_4': $i).
% 7.83/2.87  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 7.83/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.83/2.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.83/2.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.83/2.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.83/2.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.83/2.87  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.83/2.87  
% 7.83/2.88  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.83/2.88  tff(f_119, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 7.83/2.88  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 7.83/2.88  tff(f_88, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.83/2.88  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 7.83/2.88  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 7.83/2.88  tff(f_65, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 7.83/2.88  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 7.83/2.88  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 7.83/2.88  tff(f_94, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 7.83/2.88  tff(f_103, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 7.83/2.88  tff(f_109, axiom, (![A, B, C]: ((r2_hidden(A, B) & r1_tarski(A, C)) => r1_tarski(k1_setfam_1(B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_setfam_1)).
% 7.83/2.88  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.83/2.88  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.83/2.88  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.83/2.88  tff(c_502, plain, (![A_92, B_93]: (m1_subset_1(k8_setfam_1(A_92, B_93), k1_zfmisc_1(A_92)) | ~m1_subset_1(B_93, k1_zfmisc_1(k1_zfmisc_1(A_92))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.83/2.88  tff(c_44, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.83/2.88  tff(c_593, plain, (![A_104, B_105]: (r1_tarski(k8_setfam_1(A_104, B_105), A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(k1_zfmisc_1(A_104))))), inference(resolution, [status(thm)], [c_502, c_44])).
% 7.83/2.88  tff(c_617, plain, (r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_60, c_593])).
% 7.83/2.88  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.83/2.88  tff(c_280, plain, (![A_73, B_74]: (k6_setfam_1(A_73, B_74)=k1_setfam_1(B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1(A_73))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.83/2.88  tff(c_302, plain, (k6_setfam_1('#skF_4', '#skF_5')=k1_setfam_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_280])).
% 7.83/2.88  tff(c_760, plain, (![A_113, B_114]: (k8_setfam_1(A_113, B_114)=k6_setfam_1(A_113, B_114) | k1_xboole_0=B_114 | ~m1_subset_1(B_114, k1_zfmisc_1(k1_zfmisc_1(A_113))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.83/2.88  tff(c_782, plain, (k8_setfam_1('#skF_4', '#skF_5')=k6_setfam_1('#skF_4', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_62, c_760])).
% 7.83/2.88  tff(c_795, plain, (k8_setfam_1('#skF_4', '#skF_5')=k1_setfam_1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_302, c_782])).
% 7.83/2.88  tff(c_829, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_795])).
% 7.83/2.88  tff(c_34, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.83/2.88  tff(c_36, plain, (![A_17]: (k8_setfam_1(A_17, k1_xboole_0)=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.83/2.88  tff(c_64, plain, (![A_17]: (k8_setfam_1(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36])).
% 7.83/2.88  tff(c_847, plain, (![A_17]: (k8_setfam_1(A_17, '#skF_5')=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_829, c_64])).
% 7.83/2.88  tff(c_618, plain, (r1_tarski(k8_setfam_1('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_62, c_593])).
% 7.83/2.88  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.83/2.88  tff(c_632, plain, (k8_setfam_1('#skF_4', '#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k8_setfam_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_618, c_2])).
% 7.83/2.88  tff(c_759, plain, (~r1_tarski('#skF_4', k8_setfam_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_632])).
% 7.83/2.88  tff(c_901, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_847, c_759])).
% 7.83/2.88  tff(c_906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_901])).
% 7.83/2.88  tff(c_908, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_795])).
% 7.83/2.88  tff(c_58, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.83/2.88  tff(c_46, plain, (![A_23, B_24]: (m1_subset_1(A_23, k1_zfmisc_1(B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.83/2.88  tff(c_12, plain, (![C_8, A_4]: (r2_hidden(C_8, k1_zfmisc_1(A_4)) | ~r1_tarski(C_8, A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.83/2.88  tff(c_182, plain, (![C_59, A_60, B_61]: (r2_hidden(C_59, A_60) | ~r2_hidden(C_59, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.83/2.88  tff(c_1467, plain, (![C_157, A_158, A_159]: (r2_hidden(C_157, A_158) | ~m1_subset_1(k1_zfmisc_1(A_159), k1_zfmisc_1(A_158)) | ~r1_tarski(C_157, A_159))), inference(resolution, [status(thm)], [c_12, c_182])).
% 7.83/2.88  tff(c_1717, plain, (![C_173, B_174, A_175]: (r2_hidden(C_173, B_174) | ~r1_tarski(C_173, A_175) | ~r1_tarski(k1_zfmisc_1(A_175), B_174))), inference(resolution, [status(thm)], [c_46, c_1467])).
% 7.83/2.88  tff(c_1766, plain, (![B_176]: (r2_hidden('#skF_5', B_176) | ~r1_tarski(k1_zfmisc_1('#skF_6'), B_176))), inference(resolution, [status(thm)], [c_58, c_1717])).
% 7.83/2.88  tff(c_1771, plain, (r2_hidden('#skF_5', k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_6, c_1766])).
% 7.83/2.88  tff(c_517, plain, (![A_17]: (m1_subset_1(A_17, k1_zfmisc_1(A_17)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_17))))), inference(superposition, [status(thm), theory('equality')], [c_64, c_502])).
% 7.83/2.88  tff(c_524, plain, (![A_94]: (m1_subset_1(A_94, k1_zfmisc_1(A_94)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_517])).
% 7.83/2.88  tff(c_48, plain, (![A_25, C_27, B_26]: (m1_subset_1(A_25, C_27) | ~m1_subset_1(B_26, k1_zfmisc_1(C_27)) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.83/2.88  tff(c_541, plain, (![A_25, A_94]: (m1_subset_1(A_25, A_94) | ~r2_hidden(A_25, A_94))), inference(resolution, [status(thm)], [c_524, c_48])).
% 7.83/2.88  tff(c_1789, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_1771, c_541])).
% 7.83/2.88  tff(c_420, plain, (![A_86, B_87]: (r2_hidden('#skF_3'(A_86, B_87), A_86) | r1_tarski(B_87, k1_setfam_1(A_86)) | k1_xboole_0=A_86)), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.83/2.88  tff(c_32, plain, (![C_15, A_12, B_13]: (r2_hidden(C_15, A_12) | ~r2_hidden(C_15, B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.83/2.88  tff(c_435, plain, (![A_86, B_87, A_12]: (r2_hidden('#skF_3'(A_86, B_87), A_12) | ~m1_subset_1(A_86, k1_zfmisc_1(A_12)) | r1_tarski(B_87, k1_setfam_1(A_86)) | k1_xboole_0=A_86)), inference(resolution, [status(thm)], [c_420, c_32])).
% 7.83/2.88  tff(c_190, plain, (![B_62, C_63, A_64]: (r1_tarski(k1_setfam_1(B_62), C_63) | ~r1_tarski(A_64, C_63) | ~r2_hidden(A_64, B_62))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.83/2.88  tff(c_203, plain, (![B_62, B_2]: (r1_tarski(k1_setfam_1(B_62), B_2) | ~r2_hidden(B_2, B_62))), inference(resolution, [status(thm)], [c_6, c_190])).
% 7.83/2.88  tff(c_633, plain, (![B_106, A_107]: (~r1_tarski(B_106, '#skF_3'(A_107, B_106)) | r1_tarski(B_106, k1_setfam_1(A_107)) | k1_xboole_0=A_107)), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.83/2.88  tff(c_7847, plain, (![B_354, A_355]: (r1_tarski(k1_setfam_1(B_354), k1_setfam_1(A_355)) | k1_xboole_0=A_355 | ~r2_hidden('#skF_3'(A_355, k1_setfam_1(B_354)), B_354))), inference(resolution, [status(thm)], [c_203, c_633])).
% 7.83/2.88  tff(c_8971, plain, (![A_381, A_382]: (~m1_subset_1(A_381, k1_zfmisc_1(A_382)) | r1_tarski(k1_setfam_1(A_382), k1_setfam_1(A_381)) | k1_xboole_0=A_381)), inference(resolution, [status(thm)], [c_435, c_7847])).
% 7.83/2.88  tff(c_907, plain, (k8_setfam_1('#skF_4', '#skF_5')=k1_setfam_1('#skF_5')), inference(splitRight, [status(thm)], [c_795])).
% 7.83/2.88  tff(c_301, plain, (k6_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_280])).
% 7.83/2.88  tff(c_779, plain, (k8_setfam_1('#skF_4', '#skF_6')=k6_setfam_1('#skF_4', '#skF_6') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_60, c_760])).
% 7.83/2.88  tff(c_793, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6') | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_301, c_779])).
% 7.83/2.88  tff(c_799, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_793])).
% 7.83/2.88  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.83/2.88  tff(c_817, plain, (![A_3]: (r1_tarski('#skF_6', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_799, c_8])).
% 7.83/2.88  tff(c_148, plain, (![B_56, A_57]: (B_56=A_57 | ~r1_tarski(B_56, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.83/2.88  tff(c_166, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_148])).
% 7.83/2.88  tff(c_180, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_166])).
% 7.83/2.88  tff(c_826, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_817, c_180])).
% 7.83/2.88  tff(c_827, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6')), inference(splitRight, [status(thm)], [c_793])).
% 7.83/2.88  tff(c_56, plain, (~r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), k8_setfam_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.83/2.88  tff(c_923, plain, (~r1_tarski(k1_setfam_1('#skF_6'), k8_setfam_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_827, c_56])).
% 7.83/2.88  tff(c_978, plain, (~r1_tarski(k1_setfam_1('#skF_6'), k1_setfam_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_907, c_923])).
% 7.83/2.88  tff(c_8994, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_6')) | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_8971, c_978])).
% 7.83/2.88  tff(c_9068, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1789, c_8994])).
% 7.83/2.88  tff(c_9070, plain, $false, inference(negUnitSimplification, [status(thm)], [c_908, c_9068])).
% 7.83/2.88  tff(c_9071, plain, (k8_setfam_1('#skF_4', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_632])).
% 7.83/2.88  tff(c_9074, plain, (~r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9071, c_56])).
% 7.83/2.88  tff(c_9078, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_617, c_9074])).
% 7.83/2.88  tff(c_9079, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_166])).
% 7.83/2.88  tff(c_9089, plain, (~r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), k8_setfam_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_9079, c_56])).
% 7.83/2.88  tff(c_9095, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_9089])).
% 7.83/2.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.83/2.88  
% 7.83/2.88  Inference rules
% 7.83/2.88  ----------------------
% 7.83/2.88  #Ref     : 0
% 7.83/2.88  #Sup     : 2045
% 7.83/2.88  #Fact    : 0
% 7.83/2.88  #Define  : 0
% 7.83/2.88  #Split   : 37
% 7.83/2.88  #Chain   : 0
% 7.83/2.88  #Close   : 0
% 7.83/2.88  
% 7.83/2.88  Ordering : KBO
% 7.83/2.88  
% 7.83/2.88  Simplification rules
% 7.83/2.88  ----------------------
% 7.83/2.88  #Subsume      : 493
% 7.83/2.88  #Demod        : 1294
% 7.83/2.88  #Tautology    : 661
% 7.83/2.88  #SimpNegUnit  : 104
% 7.83/2.88  #BackRed      : 166
% 7.83/2.88  
% 7.83/2.88  #Partial instantiations: 0
% 7.83/2.88  #Strategies tried      : 1
% 7.83/2.88  
% 7.83/2.88  Timing (in seconds)
% 7.83/2.88  ----------------------
% 7.83/2.89  Preprocessing        : 0.33
% 7.83/2.89  Parsing              : 0.17
% 7.83/2.89  CNF conversion       : 0.02
% 7.83/2.89  Main loop            : 1.73
% 7.83/2.89  Inferencing          : 0.48
% 7.83/2.89  Reduction            : 0.61
% 7.83/2.89  Demodulation         : 0.41
% 7.83/2.89  BG Simplification    : 0.05
% 7.83/2.89  Subsumption          : 0.46
% 7.83/2.89  Abstraction          : 0.07
% 7.83/2.89  MUC search           : 0.00
% 7.83/2.89  Cooper               : 0.00
% 7.83/2.89  Total                : 2.09
% 7.83/2.89  Index Insertion      : 0.00
% 7.83/2.89  Index Deletion       : 0.00
% 7.83/2.89  Index Matching       : 0.00
% 7.83/2.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
